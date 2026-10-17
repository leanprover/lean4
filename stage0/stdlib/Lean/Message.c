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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_ofKernelEnv(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
static lean_once_cell_t l_Lean_MessageData_formatAux___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_MessageData_formatAux___closed__7;
static const lean_string_object l_Lean_MessageData_formatAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_MessageData_formatAux___closed__8 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__8_value;
static const lean_ctor_object l_Lean_MessageData_formatAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_MessageData_formatAux___closed__8_value)}};
static const lean_object* l_Lean_MessageData_formatAux___closed__9 = (const lean_object*)&l_Lean_MessageData_formatAux___closed__9_value;
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
lean_inc_ref(v___y_41_);
v___x_43_ = lean_string_append(v___y_41_, v___y_42_);
if (lean_obj_tag(v___y_40_) == 0)
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
v_val_45_ = lean_ctor_get(v___y_40_, 0);
lean_inc(v_val_45_);
lean_dec_ref_known(v___y_40_, 1);
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
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1381_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1382_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
lean_ctor_set(v___x_1384_, 2, v___x_1383_);
lean_ctor_set(v___x_1384_, 3, v___x_1383_);
lean_ctor_set(v___x_1384_, 4, v___x_1382_);
lean_ctor_set(v___x_1384_, 5, v___x_1382_);
lean_ctor_set(v___x_1384_, 6, v___x_1382_);
lean_ctor_set(v___x_1384_, 7, v___x_1382_);
lean_ctor_set(v___x_1384_, 8, v___x_1382_);
lean_ctor_set(v___x_1384_, 9, v___x_1382_);
lean_ctor_set(v___x_1384_, 10, v___x_1382_);
lean_ctor_set(v___x_1384_, 11, v___x_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1385_, lean_object* v_a_1386_){
_start:
{
switch(lean_obj_tag(v_a_1386_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1385_) == 0)
{
lean_object* v_hasSyntheticSorry_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_hasSyntheticSorry_1387_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_hasSyntheticSorry_1387_);
lean_dec_ref_known(v_a_1386_, 2);
v___x_1388_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1389_ = lean_apply_1(v_hasSyntheticSorry_1387_, v___x_1388_);
v___x_1390_ = lean_unbox(v___x_1389_);
return v___x_1390_;
}
else
{
lean_object* v_hasSyntheticSorry_1391_; lean_object* v_val_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_hasSyntheticSorry_1391_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_hasSyntheticSorry_1391_);
lean_dec_ref_known(v_a_1386_, 2);
v_val_1392_ = lean_ctor_get(v_mctx_x3f_1385_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v_mctx_x3f_1385_, 1);
v___x_1393_ = lean_apply_1(v_hasSyntheticSorry_1391_, v_val_1392_);
v___x_1394_ = lean_unbox(v___x_1393_);
return v___x_1394_;
}
}
case 3:
{
lean_object* v_a_1395_; lean_object* v_a_1396_; lean_object* v_mctx_1397_; lean_object* v___x_1398_; 
lean_dec(v_mctx_x3f_1385_);
v_a_1395_ = lean_ctor_get(v_a_1386_, 0);
lean_inc_ref(v_a_1395_);
v_a_1396_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1396_);
lean_dec_ref_known(v_a_1386_, 2);
v_mctx_1397_ = lean_ctor_get(v_a_1395_, 1);
lean_inc_ref(v_mctx_1397_);
lean_dec_ref(v_a_1395_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_mctx_1397_);
v_mctx_x3f_1385_ = v___x_1398_;
v_a_1386_ = v_a_1396_;
goto _start;
}
case 4:
{
lean_object* v_a_1400_; 
v_a_1400_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1400_);
lean_dec_ref_known(v_a_1386_, 2);
v_a_1386_ = v_a_1400_;
goto _start;
}
case 5:
{
lean_object* v_a_1402_; 
v_a_1402_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1402_);
lean_dec_ref_known(v_a_1386_, 2);
v_a_1386_ = v_a_1402_;
goto _start;
}
case 6:
{
lean_object* v_a_1404_; 
v_a_1404_ = lean_ctor_get(v_a_1386_, 0);
lean_inc_ref(v_a_1404_);
lean_dec_ref_known(v_a_1386_, 1);
v_a_1386_ = v_a_1404_;
goto _start;
}
case 7:
{
lean_object* v_a_1406_; lean_object* v_a_1407_; uint8_t v___x_1408_; 
v_a_1406_ = lean_ctor_get(v_a_1386_, 0);
lean_inc_ref(v_a_1406_);
v_a_1407_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1407_);
lean_dec_ref_known(v_a_1386_, 2);
lean_inc(v_mctx_x3f_1385_);
v___x_1408_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1385_, v_a_1406_);
if (v___x_1408_ == 0)
{
v_a_1386_ = v_a_1407_;
goto _start;
}
else
{
lean_dec_ref(v_a_1407_);
lean_dec(v_mctx_x3f_1385_);
return v___x_1408_;
}
}
case 8:
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1410_);
lean_dec_ref_known(v_a_1386_, 2);
v_a_1386_ = v_a_1410_;
goto _start;
}
case 11:
{
lean_object* v_a_1412_; 
v_a_1412_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_a_1412_);
lean_dec_ref_known(v_a_1386_, 2);
v_a_1386_ = v_a_1412_;
goto _start;
}
case 9:
{
lean_object* v_msg_1414_; lean_object* v_children_1415_; uint8_t v___x_1416_; 
v_msg_1414_ = lean_ctor_get(v_a_1386_, 1);
lean_inc_ref(v_msg_1414_);
v_children_1415_ = lean_ctor_get(v_a_1386_, 2);
lean_inc_ref(v_children_1415_);
lean_dec_ref_known(v_a_1386_, 3);
lean_inc(v_mctx_x3f_1385_);
v___x_1416_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1385_, v_msg_1414_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v_children_1415_);
v___x_1419_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_dec_ref(v_children_1415_);
lean_dec(v_mctx_x3f_1385_);
return v___x_1419_;
}
else
{
if (v___x_1419_ == 0)
{
lean_dec_ref(v_children_1415_);
lean_dec(v_mctx_x3f_1385_);
return v___x_1419_;
}
else
{
size_t v___x_1420_; size_t v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1418_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1385_, v_children_1415_, v___x_1420_, v___x_1421_);
lean_dec_ref(v_children_1415_);
return v___x_1422_;
}
}
}
else
{
lean_dec_ref(v_children_1415_);
lean_dec(v_mctx_x3f_1385_);
return v___x_1416_;
}
}
default: 
{
uint8_t v___x_1423_; 
lean_dec_ref(v_a_1386_);
lean_dec(v_mctx_x3f_1385_);
v___x_1423_ = 0;
return v___x_1423_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1424_, lean_object* v_as_1425_, size_t v_i_1426_, size_t v_stop_1427_){
_start:
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_eq(v_i_1426_, v_stop_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_uget_borrowed(v_as_1425_, v_i_1426_);
lean_inc(v___x_1429_);
lean_inc(v_mctx_x3f_1424_);
v___x_1430_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1424_, v___x_1429_);
if (v___x_1430_ == 0)
{
size_t v___x_1431_; size_t v___x_1432_; 
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1426_, v___x_1431_);
v_i_1426_ = v___x_1432_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1424_);
return v___x_1430_;
}
}
else
{
uint8_t v___x_1434_; 
lean_dec(v_mctx_x3f_1424_);
v___x_1434_ = 0;
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1435_, lean_object* v_as_1436_, lean_object* v_i_1437_, lean_object* v_stop_1438_){
_start:
{
size_t v_i_boxed_1439_; size_t v_stop_boxed_1440_; uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_i_boxed_1439_ = lean_unbox_usize(v_i_1437_);
lean_dec(v_i_1437_);
v_stop_boxed_1440_ = lean_unbox_usize(v_stop_1438_);
lean_dec(v_stop_1438_);
v_res_1441_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1435_, v_as_1436_, v_i_boxed_1439_, v_stop_boxed_1440_);
lean_dec_ref(v_as_1436_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1443_, lean_object* v_a_1444_){
_start:
{
uint8_t v_res_1445_; lean_object* v_r_1446_; 
v_res_1445_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1443_, v_a_1444_);
v_r_1446_ = lean_box(v_res_1445_);
return v_r_1446_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1447_){
_start:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_box(0);
v___x_1449_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1448_, v_msg_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1450_){
_start:
{
uint8_t v_res_1451_; lean_object* v_r_1452_; 
v_res_1451_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1450_);
v_r_1452_ = lean_box(v_res_1451_);
return v_r_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object* v_name_1453_, lean_object* v_decl_1454_, lean_object* v_ref_1455_){
_start:
{
lean_object* v_defValue_1457_; lean_object* v_descr_1458_; lean_object* v_deprecation_x3f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_defValue_1457_ = lean_ctor_get(v_decl_1454_, 0);
v_descr_1458_ = lean_ctor_get(v_decl_1454_, 1);
v_deprecation_x3f_1459_ = lean_ctor_get(v_decl_1454_, 2);
lean_inc(v_defValue_1457_);
v___x_1460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_defValue_1457_);
lean_inc(v_deprecation_x3f_1459_);
lean_inc_ref(v_descr_1458_);
lean_inc_n(v_name_1453_, 2);
v___x_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1461_, 0, v_name_1453_);
lean_ctor_set(v___x_1461_, 1, v_ref_1455_);
lean_ctor_set(v___x_1461_, 2, v___x_1460_);
lean_ctor_set(v___x_1461_, 3, v_descr_1458_);
lean_ctor_set(v___x_1461_, 4, v_deprecation_x3f_1459_);
v___x_1462_ = lean_register_option(v_name_1453_, v___x_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1471_);
v___x_1464_ = v___x_1462_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v___x_1462_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_inc(v_defValue_1457_);
v___x_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1466_, 0, v_name_1453_);
lean_ctor_set(v___x_1466_, 1, v_defValue_1457_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_name_1453_);
v_a_1472_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1462_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1462_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1480_, lean_object* v_decl_1481_, lean_object* v_ref_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1480_, v_decl_1481_, v_ref_1482_);
lean_dec_ref(v_decl_1481_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1499_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1500_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1501_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v___x_1498_, v___x_1499_, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object* v_a_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_nat_to_int(v_a_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = l_instMonadBaseIO;
v___x_1508_ = l_instInhabitedOfMonad___redArg(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1610__overap_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1610__overap_1512_ = lean_panic_fn_borrowed(v___x_1511_, v_msg_1509_);
v___x_1513_ = lean_apply_1(v___x_1610__overap_1512_, lean_box(0));
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_dec(v_x_1517_);
return v_x_1518_;
}
else
{
lean_object* v_head_1520_; lean_object* v_tail_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1530_; 
v_head_1520_ = lean_ctor_get(v_x_1519_, 0);
v_tail_1521_ = lean_ctor_get(v_x_1519_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1519_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1523_ = v_x_1519_;
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_tail_1521_);
lean_inc(v_head_1520_);
lean_dec(v_x_1519_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1530_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
lean_inc(v_x_1517_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 5);
lean_ctor_set(v___x_1523_, 1, v_x_1517_);
lean_ctor_set(v___x_1523_, 0, v_x_1518_);
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_x_1518_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_x_1517_);
v___x_1526_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v_head_1520_);
v_x_1518_ = v___x_1527_;
v_x_1519_ = v_tail_1521_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
if (lean_obj_tag(v_x_1531_) == 0)
{
lean_object* v___x_1533_; 
lean_dec(v_x_1532_);
v___x_1533_ = lean_box(0);
return v___x_1533_;
}
else
{
lean_object* v_tail_1534_; 
v_tail_1534_ = lean_ctor_get(v_x_1531_, 1);
if (lean_obj_tag(v_tail_1534_) == 0)
{
lean_object* v_head_1535_; 
lean_dec(v_x_1532_);
v_head_1535_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_head_1535_);
lean_dec_ref_known(v_x_1531_, 2);
return v_head_1535_;
}
else
{
lean_object* v_head_1536_; lean_object* v___x_1537_; 
lean_inc(v_tail_1534_);
v_head_1536_ = lean_ctor_get(v_x_1531_, 0);
lean_inc(v_head_1536_);
lean_dec_ref_known(v_x_1531_, 2);
v___x_1537_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1532_, v_head_1536_, v_tail_1534_);
return v___x_1537_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__7(void){
_start:
{
lean_object* v___x_1549_; double v___x_1550_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = lean_float_of_nat(v___x_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
switch(lean_obj_tag(v_x_1559_))
{
case 0:
{
lean_object* v_a_1561_; lean_object* v_fmt_1562_; 
lean_dec(v_x_1558_);
lean_dec_ref(v_x_1557_);
v_a_1561_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_a_1561_);
lean_dec_ref_known(v_x_1559_, 1);
v_fmt_1562_ = lean_ctor_get(v_a_1561_, 0);
lean_inc(v_fmt_1562_);
lean_dec_ref(v_a_1561_);
return v_fmt_1562_;
}
case 1:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_x_1557_);
v_a_1563_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1564_ = l_Lean_formatRawGoal(v_a_1563_);
return v___x_1564_;
}
else
{
lean_object* v_a_1565_; lean_object* v_val_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_a_1565_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v_x_1559_, 1);
v_val_1566_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_x_1558_, 1);
v___x_1567_ = l_Lean_MessageData_mkPPContext(v_x_1557_, v_val_1566_);
lean_dec(v_val_1566_);
lean_dec_ref(v_x_1557_);
v___x_1568_ = l_Lean_ppGoal(v___x_1567_, v_a_1565_);
return v___x_1568_;
}
}
case 3:
{
lean_object* v_a_1569_; lean_object* v_a_1570_; lean_object* v___x_1571_; 
lean_dec(v_x_1558_);
v_a_1569_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_a_1569_);
v_a_1570_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_a_1570_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_a_1569_);
v_x_1558_ = v___x_1571_;
v_x_1559_ = v_a_1570_;
goto _start;
}
case 4:
{
lean_object* v_a_1573_; lean_object* v_a_1574_; 
lean_dec_ref(v_x_1557_);
v_a_1573_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_a_1573_);
v_a_1574_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_a_1574_);
lean_dec_ref_known(v_x_1559_, 2);
v_x_1557_ = v_a_1573_;
v_x_1559_ = v_a_1574_;
goto _start;
}
case 5:
{
lean_object* v_a_1576_; lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1586_; 
v_a_1576_ = lean_ctor_get(v_x_1559_, 0);
v_a_1577_ = lean_ctor_get(v_x_1559_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1579_ = v_x_1559_;
v_isShared_1580_ = v_isSharedCheck_1586_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_inc(v_a_1576_);
lean_dec(v_x_1559_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1586_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1581_ = l_Lean_MessageData_formatAux(v_x_1557_, v_x_1558_, v_a_1577_);
v___x_1582_ = lean_nat_to_int(v_a_1576_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 4);
lean_ctor_set(v___x_1579_, 1, v___x_1581_);
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1581_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
case 6:
{
lean_object* v_a_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; 
v_a_1587_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_a_1587_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1588_ = l_Lean_MessageData_formatAux(v_x_1557_, v_x_1558_, v_a_1587_);
v___x_1589_ = 0;
v___x_1590_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*1, v___x_1589_);
return v___x_1590_;
}
case 7:
{
lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1601_; 
v_a_1591_ = lean_ctor_get(v_x_1559_, 0);
v_a_1592_ = lean_ctor_get(v_x_1559_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1559_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1594_ = v_x_1559_;
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_inc(v_a_1591_);
lean_dec(v_x_1559_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_inc(v_x_1558_);
lean_inc_ref(v_x_1557_);
v___x_1596_ = l_Lean_MessageData_formatAux(v_x_1557_, v_x_1558_, v_a_1591_);
v___x_1597_ = l_Lean_MessageData_formatAux(v_x_1557_, v_x_1558_, v_a_1592_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 5);
lean_ctor_set(v___x_1594_, 1, v___x_1597_);
lean_ctor_set(v___x_1594_, 0, v___x_1596_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
case 9:
{
lean_object* v_data_1602_; lean_object* v_msg_1603_; lean_object* v_children_1604_; size_t v_sz_1605_; size_t v___x_1606_; lean_object* v___x_1607_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v_cls_1621_; lean_object* v_result_x3f_1622_; double v_startTime_1623_; double v_stopTime_1624_; lean_object* v_msg_1626_; uint8_t v___x_1641_; 
v_data_1602_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_data_1602_);
v_msg_1603_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_msg_1603_);
v_children_1604_ = lean_ctor_get(v_x_1559_, 2);
lean_inc_ref(v_children_1604_);
lean_dec_ref_known(v_x_1559_, 3);
v_sz_1605_ = lean_array_size(v_children_1604_);
v___x_1606_ = ((size_t)0ULL);
lean_inc(v_x_1558_);
lean_inc_ref(v_x_1557_);
v___x_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1557_, v_x_1558_, v_sz_1605_, v___x_1606_, v_children_1604_);
v_cls_1621_ = lean_ctor_get(v_data_1602_, 0);
lean_inc(v_cls_1621_);
v_result_x3f_1622_ = lean_ctor_get(v_data_1602_, 1);
lean_inc(v_result_x3f_1622_);
v_startTime_1623_ = lean_ctor_get_float(v_data_1602_, sizeof(void*)*3);
v_stopTime_1624_ = lean_ctor_get_float(v_data_1602_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1602_);
v___x_1641_ = l_Lean_Name_isAnonymous(v_cls_1621_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; double v___x_1649_; uint8_t v___x_1650_; 
v___x_1642_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1643_ = 1;
v___x_1644_ = l_Lean_Name_toString(v_cls_1621_, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
v___x_1646_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1642_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1648_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__7, &l_Lean_MessageData_formatAux___closed__7_once, _init_l_Lean_MessageData_formatAux___closed__7);
v___x_1650_ = lean_float_beq(v_startTime_1623_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; double v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1651_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__9));
v___x_1652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1648_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_float_sub(v_stopTime_1624_, v_startTime_1623_);
v___x_1654_ = lean_float_to_string(v___x_1653_);
v___x_1655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1652_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v___x_1647_);
v_msg_1626_ = v___x_1657_;
goto v___jp_1625_;
}
else
{
v_msg_1626_ = v___x_1648_;
goto v___jp_1625_;
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_dec(v_result_x3f_1622_);
lean_dec(v_cls_1621_);
lean_dec_ref(v_msg_1603_);
lean_dec(v_x_1558_);
lean_dec_ref(v_x_1557_);
v___x_1658_ = lean_array_to_list(v___x_1607_);
v___x_1659_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1660_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1658_, v___x_1659_);
return v___x_1660_;
}
v___jp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1611_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___y_1609_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1614_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___y_1610_);
v___x_1615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1612_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_array_to_list(v___x_1607_);
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1619_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1613_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
return v___x_1620_;
}
v___jp_1625_:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_MessageData_formatAux(v_x_1557_, v_x_1558_, v_msg_1603_);
if (lean_obj_tag(v_result_x3f_1622_) == 0)
{
v___y_1609_ = v_msg_1626_;
v___y_1610_ = v___x_1627_;
goto v___jp_1608_;
}
else
{
lean_object* v_val_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1640_; 
v_val_1628_ = lean_ctor_get(v_result_x3f_1622_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_result_x3f_1622_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1630_ = v_result_x3f_1622_;
v_isShared_1631_ = v_isSharedCheck_1640_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_val_1628_);
lean_dec(v_result_x3f_1622_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1640_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1632_ = lean_unbox(v_val_1628_);
lean_dec(v_val_1628_);
v___x_1633_ = l_Lean_TraceResult_toEmoji(v___x_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 3);
lean_ctor_set(v___x_1630_, 0, v___x_1633_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1627_);
v___y_1609_ = v_msg_1626_;
v___y_1610_ = v___x_1638_;
goto v___jp_1608_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1661_; lean_object* v___x_1662_; lean_object* v___y_1664_; 
v_f_1661_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_f_1661_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1662_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_box(0);
v___y_1664_ = v___x_1680_;
goto v___jp_1663_;
}
else
{
lean_object* v_val_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_val_1681_ = lean_ctor_get(v_x_1558_, 0);
v___x_1682_ = l_Lean_MessageData_mkPPContext(v_x_1557_, v_val_1681_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
v___y_1664_ = v___x_1683_;
goto v___jp_1663_;
}
v___jp_1663_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_apply_2(v_f_1661_, v___y_1664_, lean_box(0));
v___x_1666_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1665_, v___x_1662_);
if (lean_obj_tag(v___x_1666_) == 1)
{
lean_object* v_val_1667_; 
lean_dec(v___x_1665_);
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v_x_1559_ = v_val_1667_;
goto _start;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v___x_1666_);
lean_dec(v_x_1558_);
lean_dec_ref(v_x_1557_);
v___x_1669_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1670_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1671_ = lean_unsigned_to_nat(409u);
v___x_1672_ = lean_unsigned_to_nat(8u);
v___x_1673_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1674_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1665_);
lean_dec(v___x_1665_);
v___x_1675_ = 1;
v___x_1676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1674_, v___x_1675_);
v___x_1677_ = lean_string_append(v___x_1673_, v___x_1676_);
lean_dec_ref(v___x_1676_);
v___x_1678_ = l_mkPanicMessageWithDecl(v___x_1669_, v___x_1670_, v___x_1671_, v___x_1672_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1678_);
return v___x_1679_;
}
}
}
default: 
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_a_1684_);
lean_dec_ref(v_x_1559_);
v_x_1559_ = v_a_1684_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1686_, lean_object* v_x_1687_, size_t v_sz_1688_, size_t v_i_1689_, lean_object* v_bs_1690_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_lt(v_i_1689_, v_sz_1688_);
if (v___x_1692_ == 0)
{
lean_dec(v_x_1687_);
lean_dec_ref(v_x_1686_);
return v_bs_1690_;
}
else
{
lean_object* v_v_1693_; lean_object* v___x_1694_; lean_object* v_bs_x27_1695_; lean_object* v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; lean_object* v___x_1699_; 
v_v_1693_ = lean_array_uget(v_bs_1690_, v_i_1689_);
v___x_1694_ = lean_unsigned_to_nat(0u);
v_bs_x27_1695_ = lean_array_uset(v_bs_1690_, v_i_1689_, v___x_1694_);
lean_inc(v_x_1687_);
lean_inc_ref(v_x_1686_);
v___x_1696_ = l_Lean_MessageData_formatAux(v_x_1686_, v_x_1687_, v_v_1693_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1689_, v___x_1697_);
v___x_1699_ = lean_array_uset(v_bs_x27_1695_, v_i_1689_, v___x_1696_);
v_i_1689_ = v___x_1698_;
v_bs_1690_ = v___x_1699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_sz_1703_, lean_object* v_i_1704_, lean_object* v_bs_1705_, lean_object* v___y_1706_){
_start:
{
size_t v_sz_boxed_1707_; size_t v_i_boxed_1708_; lean_object* v_res_1709_; 
v_sz_boxed_1707_ = lean_unbox_usize(v_sz_1703_);
lean_dec(v_sz_1703_);
v_i_boxed_1708_ = lean_unbox_usize(v_i_1704_);
lean_dec(v_i_1704_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1701_, v_x_1702_, v_sz_boxed_1707_, v_i_boxed_1708_, v_bs_1705_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_MessageData_formatAux(v_x_1710_, v_x_1711_, v_x_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1718_, lean_object* v_ctx_x3f_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1722_ = l_Lean_MessageData_formatAux(v___x_1721_, v_ctx_x3f_1719_, v_msgData_1718_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1723_, lean_object* v_ctx_x3f_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_MessageData_format(v_msgData_1723_, v_ctx_x3f_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1729_ = lean_box(0);
v___x_1730_ = l_Lean_MessageData_format(v_msgData_1727_, v___x_1729_);
v___x_1731_ = l_Std_Format_defWidth;
v___x_1732_ = lean_unsigned_to_nat(0u);
v___x_1733_ = l_Std_Format_pretty(v___x_1730_, v___x_1731_, v___x_1732_, v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_MessageData_toString(v_msgData_1734_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_a_1737_);
lean_ctor_set(v___x_1739_, 1, v_a_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_s_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_a_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1767_ = l_Lean_MessageData_ofFormat(v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1768_){
_start:
{
if (lean_obj_tag(v_o_1768_) == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1769_;
}
else
{
lean_object* v_val_1770_; lean_object* v___x_1771_; 
v_val_1770_ = lean_ctor_get(v_o_1768_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v_o_1768_, 1);
v___x_1771_ = l_Lean_MessageData_ofExpr(v_val_1770_);
return v___x_1771_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1775_ = l_Lean_MessageData_ofFormat(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1780_ = l_Lean_MessageData_ofFormat(v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1781_, lean_object* v_i_1782_, lean_object* v_acc_1783_){
_start:
{
lean_object* v___y_1785_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_array_get_size(v_es_1781_);
v___x_1790_ = lean_nat_dec_lt(v_i_1782_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v_i_1782_);
v___x_1791_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_acc_1783_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
return v___x_1792_;
}
else
{
lean_object* v_e_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_e_1793_ = lean_array_fget_borrowed(v_es_1781_, v_i_1782_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_nat_dec_eq(v_i_1782_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_acc_1783_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
lean_inc(v_e_1793_);
v___x_1798_ = l_Lean_MessageData_ofExpr(v_e_1793_);
v___x_1799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
v___y_1785_ = v___x_1799_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_inc(v_e_1793_);
v___x_1800_ = l_Lean_MessageData_ofExpr(v_e_1793_);
v___x_1801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1801_, 0, v_acc_1783_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___y_1785_ = v___x_1801_;
goto v___jp_1784_;
}
}
v___jp_1784_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_add(v_i_1782_, v___x_1786_);
lean_dec(v_i_1782_);
v_i_1782_ = v___x_1787_;
v_acc_1783_ = v___y_1785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1802_, lean_object* v_i_1803_, lean_object* v_acc_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1802_, v_i_1803_, v_acc_1804_);
lean_dec_ref(v_es_1802_);
return v_res_1805_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1810_ = l_Lean_MessageData_ofFormat(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1814_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1811_, v___x_1812_, v___x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1815_);
lean_dec_ref(v_es_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1819_, lean_object* v_f_1820_, lean_object* v_r_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1822_ = lean_string_length(v_l_1819_);
v___x_1823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_l_1819_);
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v_f_1820_);
v___x_1826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_r_1821_);
v___x_1827_ = l_Lean_MessageData_ofFormat(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1825_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1822_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1833_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1834_ = l_Lean_MessageData_bracket(v___x_1832_, v_f_1831_, v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1837_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1838_ = l_Lean_MessageData_bracket(v___x_1836_, v_f_1835_, v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v_x_1840_);
v___x_1841_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1841_;
}
else
{
lean_object* v_tail_1842_; 
v_tail_1842_ = lean_ctor_get(v_x_1839_, 1);
if (lean_obj_tag(v_tail_1842_) == 0)
{
lean_object* v_head_1843_; 
lean_dec_ref(v_x_1840_);
v_head_1843_ = lean_ctor_get(v_x_1839_, 0);
lean_inc(v_head_1843_);
lean_dec_ref_known(v_x_1839_, 2);
return v_head_1843_;
}
else
{
lean_object* v_head_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1853_; 
lean_inc(v_tail_1842_);
v_head_1844_ = lean_ctor_get(v_x_1839_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_x_1839_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_x_1839_, 1);
lean_dec(v_unused_1854_);
v___x_1846_ = v_x_1839_;
v_isShared_1847_ = v_isSharedCheck_1853_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_head_1844_);
lean_dec(v_x_1839_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1853_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
lean_inc_ref(v_x_1840_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set_tag(v___x_1846_, 7);
lean_ctor_set(v___x_1846_, 1, v_x_1840_);
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_head_1844_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_x_1840_);
v___x_1849_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = l_Lean_MessageData_joinSep(v_tail_1842_, v_x_1840_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
return v___x_1851_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1859_ = l_Lean_MessageData_ofFormat(v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1864_ = l_Lean_MessageData_ofFormat(v___x_1863_);
return v___x_1864_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_box(1);
v___x_1866_ = l_Lean_MessageData_ofFormat(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1868_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v___x_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1870_){
_start:
{
if (lean_obj_tag(v_x_1870_) == 0)
{
lean_object* v___x_1871_; 
v___x_1871_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1873_ = l_Lean_MessageData_joinSep(v_x_1870_, v___x_1872_);
v___x_1874_ = l_Lean_MessageData_sbracket(v___x_1873_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_array_to_list(v_msgs_1875_);
v___x_1877_ = l_Lean_MessageData_ofList(v___x_1876_);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1882_ = l_Lean_MessageData_ofFormat(v___x_1881_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1887_ = l_Lean_MessageData_ofFormat(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1892_ = l_Lean_MessageData_ofFormat(v___x_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1893_){
_start:
{
if (lean_obj_tag(v_xs_1893_) == 0)
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1894_;
}
else
{
lean_object* v_tail_1895_; 
v_tail_1895_ = lean_ctor_get(v_xs_1893_, 1);
lean_inc(v_tail_1895_);
if (lean_obj_tag(v_tail_1895_) == 0)
{
lean_object* v_head_1896_; 
v_head_1896_ = lean_ctor_get(v_xs_1893_, 0);
lean_inc(v_head_1896_);
lean_dec_ref_known(v_xs_1893_, 2);
return v_head_1896_;
}
else
{
lean_object* v_tail_1897_; 
v_tail_1897_ = lean_ctor_get(v_tail_1895_, 1);
if (lean_obj_tag(v_tail_1897_) == 0)
{
lean_object* v_head_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1915_; 
v_head_1898_ = lean_ctor_get(v_xs_1893_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_xs_1893_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_xs_1893_, 1);
lean_dec(v_unused_1916_);
v___x_1900_ = v_xs_1893_;
v_isShared_1901_ = v_isSharedCheck_1915_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_head_1898_);
lean_dec(v_xs_1893_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1915_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_head_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1913_; 
v_head_1902_ = lean_ctor_get(v_tail_1895_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_tail_1895_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v_tail_1895_, 1);
lean_dec(v_unused_1914_);
v___x_1904_ = v_tail_1895_;
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_head_1902_);
lean_dec(v_tail_1895_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1913_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 7);
lean_ctor_set(v___x_1904_, 1, v___x_1906_);
lean_ctor_set(v___x_1904_, 0, v_head_1898_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_head_1898_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1901_ == 0)
{
lean_ctor_set_tag(v___x_1900_, 7);
lean_ctor_set(v___x_1900_, 1, v_head_1902_);
lean_ctor_set(v___x_1900_, 0, v___x_1908_);
v___x_1910_ = v___x_1900_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_head_1902_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1940_; 
v_isSharedCheck_1940_ = !lean_is_exclusive(v_tail_1895_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; lean_object* v_unused_1942_; 
v_unused_1941_ = lean_ctor_get(v_tail_1895_, 1);
lean_dec(v_unused_1941_);
v_unused_1942_ = lean_ctor_get(v_tail_1895_, 0);
lean_dec(v_unused_1942_);
v___x_1918_ = v_tail_1895_;
v_isShared_1919_ = v_isSharedCheck_1940_;
goto v_resetjp_1917_;
}
else
{
lean_dec(v_tail_1895_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1940_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1920_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1893_);
v___x_1921_ = lean_array_mk(v_xs_1893_);
v___x_1922_ = lean_array_pop(v___x_1921_);
v___x_1923_ = lean_array_to_list(v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1925_ = l_Lean_MessageData_joinSep(v___x_1923_, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1919_ == 0)
{
lean_ctor_set_tag(v___x_1918_, 7);
lean_ctor_set(v___x_1918_, 1, v___x_1926_);
lean_ctor_set(v___x_1918_, 0, v___x_1925_);
v___x_1928_ = v___x_1918_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v___x_1929_ = l_List_getLast_x21___redArg(v___x_1920_, v_xs_1893_);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_xs_1893_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; lean_object* v_unused_1938_; 
v_unused_1937_ = lean_ctor_get(v_xs_1893_, 1);
lean_dec(v_unused_1937_);
v_unused_1938_ = lean_ctor_get(v_xs_1893_, 0);
lean_dec(v_unused_1938_);
v___x_1931_ = v_xs_1893_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v_xs_1893_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 7);
lean_ctor_set(v___x_1931_, 1, v___x_1929_);
lean_ctor_set(v___x_1931_, 0, v___x_1928_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
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
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1947_ = l_Lean_MessageData_ofFormat(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1952_ = l_Lean_MessageData_ofFormat(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1953_){
_start:
{
if (lean_obj_tag(v_xs_1953_) == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1954_;
}
else
{
lean_object* v_tail_1955_; 
v_tail_1955_ = lean_ctor_get(v_xs_1953_, 1);
lean_inc(v_tail_1955_);
if (lean_obj_tag(v_tail_1955_) == 0)
{
lean_object* v_head_1956_; 
v_head_1956_ = lean_ctor_get(v_xs_1953_, 0);
lean_inc(v_head_1956_);
lean_dec_ref_known(v_xs_1953_, 2);
return v_head_1956_;
}
else
{
lean_object* v_tail_1957_; 
v_tail_1957_ = lean_ctor_get(v_tail_1955_, 1);
if (lean_obj_tag(v_tail_1957_) == 0)
{
lean_object* v_head_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1975_; 
v_head_1958_ = lean_ctor_get(v_xs_1953_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_xs_1953_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_xs_1953_, 1);
lean_dec(v_unused_1976_);
v___x_1960_ = v_xs_1953_;
v_isShared_1961_ = v_isSharedCheck_1975_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_head_1958_);
lean_dec(v_xs_1953_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1975_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_head_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1973_; 
v_head_1962_ = lean_ctor_get(v_tail_1955_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_tail_1955_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_tail_1955_, 1);
lean_dec(v_unused_1974_);
v___x_1964_ = v_tail_1955_;
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_head_1962_);
lean_dec(v_tail_1955_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 7);
lean_ctor_set(v___x_1964_, 1, v___x_1966_);
lean_ctor_set(v___x_1964_, 0, v_head_1958_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_head_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 7);
lean_ctor_set(v___x_1960_, 1, v_head_1962_);
lean_ctor_set(v___x_1960_, 0, v___x_1968_);
v___x_1970_ = v___x_1960_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_head_1962_);
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
else
{
lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2000_; 
v_isSharedCheck_2000_ = !lean_is_exclusive(v_tail_1955_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; lean_object* v_unused_2002_; 
v_unused_2001_ = lean_ctor_get(v_tail_1955_, 1);
lean_dec(v_unused_2001_);
v_unused_2002_ = lean_ctor_get(v_tail_1955_, 0);
lean_dec(v_unused_2002_);
v___x_1978_ = v_tail_1955_;
v_isShared_1979_ = v_isSharedCheck_2000_;
goto v_resetjp_1977_;
}
else
{
lean_dec(v_tail_1955_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2000_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1980_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1953_);
v___x_1981_ = lean_array_mk(v_xs_1953_);
v___x_1982_ = lean_array_pop(v___x_1981_);
v___x_1983_ = lean_array_to_list(v___x_1982_);
v___x_1984_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1985_ = l_Lean_MessageData_joinSep(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1979_ == 0)
{
lean_ctor_set_tag(v___x_1978_, 7);
lean_ctor_set(v___x_1978_, 1, v___x_1986_);
lean_ctor_set(v___x_1978_, 0, v___x_1985_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_1996_; 
v___x_1989_ = l_List_getLast_x21___redArg(v___x_1980_, v_xs_1953_);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_xs_1953_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1997_ = lean_ctor_get(v_xs_1953_, 1);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v_xs_1953_, 0);
lean_dec(v_unused_1998_);
v___x_1991_ = v_xs_1953_;
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_xs_1953_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_1996_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1994_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set_tag(v___x_1991_, 7);
lean_ctor_set(v___x_1991_, 1, v___x_1989_);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
v___x_1994_ = v___x_1991_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___x_1989_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
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
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
return v___x_2004_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2009_ = l_Lean_MessageData_ofFormat(v___x_2008_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2011_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
lean_ctor_set(v___x_2012_, 1, v___x_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v_note_2013_);
return v___x_2015_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2020_ = l_Lean_MessageData_ofFormat(v___x_2019_);
return v___x_2020_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2022_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v___x_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v_hint_2024_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2031_ = lean_box(0);
v___x_2032_ = l_List_mapTR_loop___redArg(v___x_2030_, v_es_2029_, v___x_2031_);
v___x_2033_ = l_Lean_MessageData_ofList(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2037_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2038_ = l_Lean_instInhabitedPosition_default;
v___x_2039_ = lean_box(0);
v___x_2040_ = 0;
v___x_2041_ = 2;
v___x_2042_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2042_, 0, v___x_2037_);
lean_ctor_set(v___x_2042_, 1, v___x_2038_);
lean_ctor_set(v___x_2042_, 2, v___x_2039_);
lean_ctor_set(v___x_2042_, 3, v___x_2037_);
lean_ctor_set(v___x_2042_, 4, v_inst_2036_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*5, v___x_2040_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*5 + 1, v___x_2041_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*5 + 2, v___x_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2043_, lean_object* v_inst_2044_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2048_, lean_object* v_inst_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_fileName_2065_; lean_object* v_pos_2066_; lean_object* v_endPos_2067_; uint8_t v_keepFullRange_2068_; uint8_t v_severity_2069_; uint8_t v_isSilent_2070_; lean_object* v_caption_2071_; lean_object* v_data_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_fileName_2065_ = lean_ctor_get(v_x_2064_, 0);
lean_inc_ref(v_fileName_2065_);
v_pos_2066_ = lean_ctor_get(v_x_2064_, 1);
lean_inc_ref(v_pos_2066_);
v_endPos_2067_ = lean_ctor_get(v_x_2064_, 2);
lean_inc(v_endPos_2067_);
v_keepFullRange_2068_ = lean_ctor_get_uint8(v_x_2064_, sizeof(void*)*5);
v_severity_2069_ = lean_ctor_get_uint8(v_x_2064_, sizeof(void*)*5 + 1);
v_isSilent_2070_ = lean_ctor_get_uint8(v_x_2064_, sizeof(void*)*5 + 2);
v_caption_2071_ = lean_ctor_get(v_x_2064_, 3);
lean_inc_ref(v_caption_2071_);
v_data_2072_ = lean_ctor_get(v_x_2064_, 4);
lean_inc(v_data_2072_);
lean_dec_ref(v_x_2064_);
v___x_2073_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2074_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_fileName_2065_);
v___x_2076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2076_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2080_ = l_Lean_instToJsonPosition_toJson(v_pos_2066_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
lean_ctor_set(v___x_2082_, 1, v___x_2077_);
v___x_2083_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2084_ = l_Lean_Option_toJson___redArg(v___x_2073_, v_endPos_2067_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2077_);
v___x_2087_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2088_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2088_, 0, v_keepFullRange_2068_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2077_);
v___x_2091_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2092_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2069_);
v___x_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2091_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___x_2077_);
v___x_2095_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2096_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2096_, 0, v_isSilent_2070_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v___x_2077_);
v___x_2099_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2100_, 0, v_caption_2071_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___x_2077_);
v___x_2103_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2104_ = lean_apply_1(v_inst_2063_, v_data_2072_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2077_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2077_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2102_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2098_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2094_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2090_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2086_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2082_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2078_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2116_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2117_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2115_, v___x_2114_, v___x_2116_);
v___x_2118_ = l_Lean_Json_mkObj(v___x_2117_);
lean_dec(v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2119_, lean_object* v_inst_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2120_, v_x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2124_, 0, lean_box(0));
lean_closure_set(v___x_2124_, 1, v_inst_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2125_, lean_object* v_inst_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2127_, 0, lean_box(0));
lean_closure_set(v___x_2127_, 1, v_inst_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = 1;
v___x_2134_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2135_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2134_, v___x_2133_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2138_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2139_ = lean_string_append(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = 1;
v___x_2143_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2146_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2147_ = lean_string_append(v___x_2146_, v___x_2145_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2150_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2151_ = lean_string_append(v___x_2150_, v___x_2149_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = 1;
v___x_2158_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2161_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2162_ = lean_string_append(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2164_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2165_ = lean_string_append(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = 1;
v___x_2169_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2170_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2169_, v___x_2168_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2172_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2173_ = lean_string_append(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2175_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2176_ = lean_string_append(v___x_2175_, v___x_2174_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = 1;
v___x_2181_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2184_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2185_ = lean_string_append(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2187_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2188_ = lean_string_append(v___x_2187_, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = 1;
v___x_2192_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2195_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2196_ = lean_string_append(v___x_2195_, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2198_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2199_ = lean_string_append(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = 1;
v___x_2203_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2206_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2207_ = lean_string_append(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2209_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2210_ = lean_string_append(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = 1;
v___x_2214_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2215_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2214_, v___x_2213_);
return v___x_2215_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2217_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2218_ = lean_string_append(v___x_2217_, v___x_2216_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2220_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2221_ = lean_string_append(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = 1;
v___x_2225_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2228_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2229_ = lean_string_append(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2231_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2232_ = lean_string_append(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2233_, lean_object* v_json_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2236_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2234_);
v___x_2237_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2235_, v___x_2236_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2242_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2243_ = lean_string_append(v___x_2242_, v_a_2238_);
lean_dec(v_a_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2243_);
v___x_2245_ = v___x_2240_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_a_2248_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2249_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2250_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2251_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2234_);
v___x_2252_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2249_, v___x_2251_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2257_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2258_ = lean_string_append(v___x_2257_, v_a_2253_);
lean_dec(v_a_2253_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
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
v_a_2263_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2252_, 1);
v___x_2264_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2234_);
v___x_2265_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2250_, v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
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
v___x_2270_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
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
lean_object* v_a_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v_a_2276_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2276_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2277_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2278_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2234_);
v___x_2279_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2277_, v___x_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2276_);
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2289_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2284_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2285_ = lean_string_append(v___x_2284_, v_a_2280_);
lean_dec(v_a_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2285_);
v___x_2287_ = v___x_2282_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v_a_2290_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2279_, 1);
v___x_2291_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2292_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2234_);
v___x_2293_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2291_, v___x_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v_a_2290_);
lean_dec(v_a_2276_);
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2298_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2299_ = lean_string_append(v___x_2298_, v_a_2294_);
lean_dec(v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2299_);
v___x_2301_ = v___x_2296_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
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
lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_a_2304_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2305_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2234_);
v___x_2306_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2277_, v___x_2305_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2316_; 
lean_dec(v_a_2304_);
lean_dec(v_a_2290_);
lean_dec(v_a_2276_);
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2316_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2312_ = lean_string_append(v___x_2311_, v_a_2307_);
lean_dec(v_a_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v___x_2312_);
v___x_2314_ = v___x_2309_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
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
lean_object* v_a_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2317_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2306_, 1);
v___x_2318_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2234_);
v___x_2319_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v___x_2235_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_a_2317_);
lean_dec(v_a_2304_);
lean_dec(v_a_2290_);
lean_dec(v_a_2276_);
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
lean_dec(v_json_2234_);
lean_dec_ref(v_inst_2233_);
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2329_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2324_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2325_ = lean_string_append(v___x_2324_, v_a_2320_);
lean_dec(v_a_2320_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2325_);
v___x_2327_ = v___x_2322_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2331_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2332_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2234_, v_inst_2233_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_a_2330_);
lean_dec(v_a_2317_);
lean_dec(v_a_2304_);
lean_dec(v_a_2290_);
lean_dec(v_a_2276_);
lean_dec(v_a_2263_);
lean_dec(v_a_2248_);
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
v___x_2337_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
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
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2354_; 
v_a_2343_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2345_ = v___x_2332_;
v_isShared_2346_ = v_isSharedCheck_2354_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2332_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2354_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; uint8_t v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2352_; 
v___x_2347_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2347_, 0, v_a_2248_);
lean_ctor_set(v___x_2347_, 1, v_a_2263_);
lean_ctor_set(v___x_2347_, 2, v_a_2276_);
lean_ctor_set(v___x_2347_, 3, v_a_2330_);
lean_ctor_set(v___x_2347_, 4, v_a_2343_);
v___x_2348_ = lean_unbox(v_a_2290_);
lean_dec(v_a_2290_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*5, v___x_2348_);
v___x_2349_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*5 + 1, v___x_2349_);
v___x_2350_ = lean_unbox(v_a_2317_);
lean_dec(v_a_2317_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*5 + 2, v___x_2350_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2352_ = v___x_2345_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2355_, lean_object* v_inst_2356_, lean_object* v_json_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2356_, v_json_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2360_, 0, lean_box(0));
lean_closure_set(v___x_2360_, 1, v_inst_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2361_, lean_object* v_inst_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2363_, 0, lean_box(0));
lean_closure_set(v___x_2363_, 1, v_inst_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2364_){
_start:
{
if (lean_obj_tag(v_x_2364_) == 0)
{
lean_object* v___x_2365_; 
v___x_2365_ = lean_box(0);
return v___x_2365_;
}
else
{
lean_object* v_val_2366_; lean_object* v___x_2367_; 
v_val_2366_ = lean_ctor_get(v_x_2364_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v_x_2364_, 1);
v___x_2367_ = l_Lean_instToJsonPosition_toJson(v_val_2366_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
if (lean_obj_tag(v_a_2368_) == 0)
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_array_to_list(v_a_2369_);
return v___x_2370_;
}
else
{
lean_object* v_head_2371_; lean_object* v_tail_2372_; lean_object* v___x_2373_; 
v_head_2371_ = lean_ctor_get(v_a_2368_, 0);
lean_inc(v_head_2371_);
v_tail_2372_ = lean_ctor_get(v_a_2368_, 1);
lean_inc(v_tail_2372_);
lean_dec_ref_known(v_a_2368_, 2);
v___x_2373_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2369_, v_head_2371_);
v_a_2368_ = v_tail_2372_;
v_a_2369_ = v___x_2373_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2376_){
_start:
{
lean_object* v_toBaseMessage_2377_; lean_object* v_kind_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2443_; 
v_toBaseMessage_2377_ = lean_ctor_get(v_x_2376_, 0);
v_kind_2378_ = lean_ctor_get(v_x_2376_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_x_2376_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2380_ = v_x_2376_;
v_isShared_2381_ = v_isSharedCheck_2443_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_kind_2378_);
lean_inc(v_toBaseMessage_2377_);
lean_dec(v_x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2443_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v_fileName_2382_; lean_object* v_pos_2383_; lean_object* v_endPos_2384_; uint8_t v_keepFullRange_2385_; uint8_t v_severity_2386_; uint8_t v_isSilent_2387_; lean_object* v_caption_2388_; lean_object* v_data_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v_fileName_2382_ = lean_ctor_get(v_toBaseMessage_2377_, 0);
lean_inc_ref(v_fileName_2382_);
v_pos_2383_ = lean_ctor_get(v_toBaseMessage_2377_, 1);
lean_inc_ref(v_pos_2383_);
v_endPos_2384_ = lean_ctor_get(v_toBaseMessage_2377_, 2);
lean_inc(v_endPos_2384_);
v_keepFullRange_2385_ = lean_ctor_get_uint8(v_toBaseMessage_2377_, sizeof(void*)*5);
v_severity_2386_ = lean_ctor_get_uint8(v_toBaseMessage_2377_, sizeof(void*)*5 + 1);
v_isSilent_2387_ = lean_ctor_get_uint8(v_toBaseMessage_2377_, sizeof(void*)*5 + 2);
v_caption_2388_ = lean_ctor_get(v_toBaseMessage_2377_, 3);
lean_inc_ref(v_caption_2388_);
v_data_2389_ = lean_ctor_get(v_toBaseMessage_2377_, 4);
lean_inc(v_data_2389_);
lean_dec_ref(v_toBaseMessage_2377_);
v___x_2390_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_fileName_2382_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v___x_2391_);
lean_ctor_set(v___x_2380_, 0, v___x_2390_);
v___x_2393_ = v___x_2380_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2394_ = lean_box(0);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2397_ = l_Lean_instToJsonPosition_toJson(v_pos_2383_);
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
lean_ctor_set(v___x_2399_, 1, v___x_2394_);
v___x_2400_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2401_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2384_);
v___x_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2394_);
v___x_2404_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2405_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2405_, 0, v_keepFullRange_2385_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v___x_2394_);
v___x_2408_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2409_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2386_);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_2394_);
v___x_2412_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2413_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2413_, 0, v_isSilent_2387_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2394_);
v___x_2416_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2417_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_caption_2388_);
v___x_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v___x_2394_);
v___x_2420_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_data_2389_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v___x_2394_);
v___x_2424_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2425_ = 1;
v___x_2426_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2378_, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2424_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___x_2394_);
v___x_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_2394_);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2423_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2419_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___x_2433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2415_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2411_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2407_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2403_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2399_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2395_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2440_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2438_, v___x_2439_);
v___x_2441_ = l_Lean_Json_mkObj(v___x_2440_);
lean_dec(v___x_2440_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2446_, lean_object* v_k_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = l_Lean_Json_getObjValD(v_j_2446_, v_k_2447_);
v___x_2449_ = l_Lean_Json_getStr_x3f(v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2450_, lean_object* v_k_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2450_, v_k_2451_);
lean_dec_ref(v_k_2451_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2453_, lean_object* v_k_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = l_Lean_Json_getObjValD(v_j_2453_, v_k_2454_);
v___x_2456_ = l_Lean_instFromJsonPosition_fromJson(v___x_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2457_, lean_object* v_k_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2457_, v_k_2458_);
lean_dec_ref(v_k_2458_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2460_, lean_object* v_k_2461_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = l_Lean_Json_getObjValD(v_j_2460_, v_k_2461_);
v___x_2463_ = l_Lean_Json_getBool_x3f(v___x_2462_);
lean_dec(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2464_, lean_object* v_k_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2464_, v_k_2465_);
lean_dec_ref(v_k_2465_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = l_Lean_Json_getObjValD(v_j_2467_, v_k_2468_);
v___x_2470_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2471_, lean_object* v_k_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2471_, v_k_2472_);
lean_dec_ref(v_k_2472_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2474_, lean_object* v_k_2475_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = l_Lean_Json_getObjValD(v_j_2474_, v_k_2475_);
v___x_2477_ = l_Lean_Name_fromJson_x3f(v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2478_, lean_object* v_k_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2478_, v_k_2479_);
lean_dec_ref(v_k_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2483_){
_start:
{
if (lean_obj_tag(v_x_2483_) == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_instFromJsonPosition_fromJson(v_x_2483_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2502_; 
v_a_2494_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2496_ = v___x_2485_;
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2485_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2502_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2494_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2503_, lean_object* v_k_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = l_Lean_Json_getObjValD(v_j_2503_, v_k_2504_);
v___x_2506_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2507_, lean_object* v_k_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2507_, v_k_2508_);
lean_dec_ref(v_k_2508_);
return v_res_2509_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = 1;
v___x_2515_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2516_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2517_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2518_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2519_ = lean_string_append(v___x_2518_, v___x_2517_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2521_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2522_ = lean_string_append(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2524_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2525_ = lean_string_append(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2527_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2528_ = lean_string_append(v___x_2527_, v___x_2526_);
return v___x_2528_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2530_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2531_ = lean_string_append(v___x_2530_, v___x_2529_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2533_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2534_ = lean_string_append(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2536_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2537_ = lean_string_append(v___x_2536_, v___x_2535_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2538_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2539_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2540_ = lean_string_append(v___x_2539_, v___x_2538_);
return v___x_2540_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2542_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2543_ = lean_string_append(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2545_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2546_ = lean_string_append(v___x_2545_, v___x_2544_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2548_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2549_ = lean_string_append(v___x_2548_, v___x_2547_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2551_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2552_ = lean_string_append(v___x_2551_, v___x_2550_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2554_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2555_ = lean_string_append(v___x_2554_, v___x_2553_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2556_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2557_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2558_ = lean_string_append(v___x_2557_, v___x_2556_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2559_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2560_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2561_ = lean_string_append(v___x_2560_, v___x_2559_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2563_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2564_ = lean_string_append(v___x_2563_, v___x_2562_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2565_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2566_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2567_ = lean_string_append(v___x_2566_, v___x_2565_);
return v___x_2567_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = 1;
v___x_2571_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2571_, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2574_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2575_ = lean_string_append(v___x_2574_, v___x_2573_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2577_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2578_ = lean_string_append(v___x_2577_, v___x_2576_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2579_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2579_);
v___x_2581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2579_, v___x_2580_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_json_2579_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2591_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2586_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2587_ = lean_string_append(v___x_2586_, v_a_2582_);
lean_dec(v_a_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v___x_2587_);
v___x_2589_ = v___x_2584_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v_a_2592_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2581_, 1);
v___x_2593_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2579_);
v___x_2594_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2579_, v___x_2593_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2604_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2604_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2600_ = lean_string_append(v___x_2599_, v_a_2595_);
lean_dec(v_a_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2600_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2605_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2594_, 1);
v___x_2606_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2579_);
v___x_2607_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2579_, v___x_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2617_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2615_; 
v___x_2612_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2613_ = lean_string_append(v___x_2612_, v_a_2608_);
lean_dec(v_a_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2613_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v_a_2618_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2619_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2579_);
v___x_2620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2579_, v___x_2619_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2630_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2630_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2628_; 
v___x_2625_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2626_ = lean_string_append(v___x_2625_, v_a_2621_);
lean_dec(v_a_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2626_);
v___x_2628_ = v___x_2623_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_a_2631_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2620_, 1);
v___x_2632_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2579_);
v___x_2633_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2579_, v___x_2632_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_a_2631_);
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2643_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2639_ = lean_string_append(v___x_2638_, v_a_2634_);
lean_dec(v_a_2634_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2639_);
v___x_2641_ = v___x_2636_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v_a_2644_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2645_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2579_);
v___x_2646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2579_, v___x_2645_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_a_2644_);
lean_dec(v_a_2631_);
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2656_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2656_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2651_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2652_ = lean_string_append(v___x_2651_, v_a_2647_);
lean_dec(v_a_2647_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2652_);
v___x_2654_ = v___x_2649_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2658_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2579_);
v___x_2659_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2579_, v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2657_);
lean_dec(v_a_2644_);
lean_dec(v_a_2631_);
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2669_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2669_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v___x_2664_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2665_ = lean_string_append(v___x_2664_, v_a_2660_);
lean_dec(v_a_2660_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2665_);
v___x_2667_ = v___x_2662_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2670_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2671_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2579_);
v___x_2672_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2579_, v___x_2671_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2670_);
lean_dec(v_a_2657_);
lean_dec(v_a_2644_);
lean_dec(v_a_2631_);
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
lean_dec(v_json_2579_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2682_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2677_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2678_ = lean_string_append(v___x_2677_, v_a_2673_);
lean_dec(v_a_2673_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2678_);
v___x_2680_ = v___x_2675_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2683_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2684_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2685_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2579_, v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2670_);
lean_dec(v_a_2657_);
lean_dec(v_a_2644_);
lean_dec(v_a_2631_);
lean_dec(v_a_2618_);
lean_dec(v_a_2605_);
lean_dec(v_a_2592_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2690_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2691_ = lean_string_append(v___x_2690_, v_a_2686_);
lean_dec(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2691_);
v___x_2693_ = v___x_2688_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2708_; 
v_a_2696_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2698_ = v___x_2685_;
v_isShared_2699_ = v_isSharedCheck_2708_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2685_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2708_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; uint8_t v___x_2701_; uint8_t v___x_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2700_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2700_, 0, v_a_2592_);
lean_ctor_set(v___x_2700_, 1, v_a_2605_);
lean_ctor_set(v___x_2700_, 2, v_a_2618_);
lean_ctor_set(v___x_2700_, 3, v_a_2670_);
lean_ctor_set(v___x_2700_, 4, v_a_2683_);
v___x_2701_ = lean_unbox(v_a_2631_);
lean_dec(v_a_2631_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*5, v___x_2701_);
v___x_2702_ = lean_unbox(v_a_2644_);
lean_dec(v_a_2644_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*5 + 1, v___x_2702_);
v___x_2703_ = lean_unbox(v_a_2657_);
lean_dec(v_a_2657_);
lean_ctor_set_uint8(v___x_2700_, sizeof(void*)*5 + 2, v___x_2703_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2700_);
lean_ctor_set(v___x_2704_, 1, v_a_2696_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 0, v___x_2704_);
v___x_2706_ = v___x_2698_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2713_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2715_ = l_Lean_Name_str___override(v_errorName_2713_, v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2716_, lean_object* v_name_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = l_Lean_kindOfErrorName(v_name_2717_);
v___x_2719_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_msg_2716_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2721_){
_start:
{
switch(lean_obj_tag(v_a_2721_))
{
case 0:
{
return v_a_2721_;
}
case 1:
{
lean_object* v_pre_2722_; lean_object* v_str_2723_; lean_object* v_p_x27_2724_; uint8_t v___x_2725_; 
v_pre_2722_ = lean_ctor_get(v_a_2721_, 0);
lean_inc(v_pre_2722_);
v_str_2723_ = lean_ctor_get(v_a_2721_, 1);
lean_inc_ref(v_str_2723_);
lean_dec_ref_known(v_a_2721_, 2);
v_p_x27_2724_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2722_);
v___x_2725_ = l_Lean_Name_isAnonymous(v_p_x27_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Name_str___override(v_p_x27_2724_, v_str_2723_);
return v___x_2726_;
}
else
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2728_ = lean_string_dec_eq(v_str_2723_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_Name_str___override(v_p_x27_2724_, v_str_2723_);
return v___x_2729_;
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_p_x27_2724_);
lean_dec_ref(v_str_2723_);
v___x_2730_ = lean_box(0);
return v___x_2730_;
}
}
}
default: 
{
lean_object* v_pre_2731_; lean_object* v_i_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_pre_2731_ = lean_ctor_get(v_a_2721_, 0);
lean_inc(v_pre_2731_);
v_i_2732_ = lean_ctor_get(v_a_2721_, 1);
lean_inc(v_i_2732_);
lean_dec_ref_known(v_a_2721_, 2);
v___x_2733_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2731_);
v___x_2734_ = l_Lean_Name_num___override(v___x_2733_, v_i_2732_);
return v___x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2735_){
_start:
{
switch(lean_obj_tag(v_x_2735_))
{
case 3:
{
lean_object* v_a_2736_; lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2745_; 
v_a_2736_ = lean_ctor_get(v_x_2735_, 0);
v_a_2737_ = lean_ctor_get(v_x_2735_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_x_2735_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2739_ = v_x_2735_;
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_inc(v_a_2736_);
lean_dec(v_x_2735_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2745_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2741_ = l_Lean_MessageData_stripNestedTags(v_a_2737_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 1, v___x_2741_);
v___x_2743_ = v___x_2739_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2736_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2741_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
case 4:
{
lean_object* v_a_2746_; lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2755_; 
v_a_2746_ = lean_ctor_get(v_x_2735_, 0);
v_a_2747_ = lean_ctor_get(v_x_2735_, 1);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_x_2735_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2749_ = v_x_2735_;
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_inc(v_a_2746_);
lean_dec(v_x_2735_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2755_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = l_Lean_MessageData_stripNestedTags(v_a_2747_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v___x_2751_);
v___x_2753_ = v___x_2749_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_a_2746_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
case 8:
{
lean_object* v_a_2756_; lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2765_; 
v_a_2756_ = lean_ctor_get(v_x_2735_, 0);
v_a_2757_ = lean_ctor_get(v_x_2735_, 1);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_x_2735_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2759_ = v_x_2735_;
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_inc(v_a_2756_);
lean_dec(v_x_2735_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2765_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2761_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2756_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2761_);
v___x_2763_ = v___x_2759_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_a_2757_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
case 11:
{
lean_object* v_a_2766_; lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2775_; 
v_a_2766_ = lean_ctor_get(v_x_2735_, 0);
v_a_2767_ = lean_ctor_get(v_x_2735_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_x_2735_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2769_ = v_x_2735_;
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_inc(v_a_2766_);
lean_dec(v_x_2735_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2775_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = l_Lean_MessageData_stripNestedTags(v_a_2767_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 1, v___x_2771_);
v___x_2773_ = v___x_2769_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2766_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
default: 
{
return v_x_2735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2776_){
_start:
{
if (lean_obj_tag(v_x_2776_) == 1)
{
lean_object* v_pre_2777_; lean_object* v_str_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v_pre_2777_ = lean_ctor_get(v_x_2776_, 0);
v_str_2778_ = lean_ctor_get(v_x_2776_, 1);
v___x_2779_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2780_ = lean_string_dec_eq(v_str_2778_, v___x_2779_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_box(0);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; 
lean_inc(v_pre_2777_);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v_pre_2777_);
return v___x_2782_;
}
}
else
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_box(0);
return v___x_2783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_errorNameOfKind_x3f(v_x_2784_);
lean_dec(v_x_2784_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = l_Lean_MessageData_kind(v_msg_2786_);
v___x_2788_ = l_Lean_errorNameOfKind_x3f(v___x_2787_);
lean_dec(v___x_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_MessageData_errorName_x3f(v_msg_2789_);
lean_dec_ref(v_msg_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2791_){
_start:
{
lean_object* v_data_2792_; lean_object* v___x_2793_; 
v_data_2792_ = lean_ctor_get(v_msg_2791_, 4);
v___x_2793_ = l_Lean_MessageData_errorName_x3f(v_data_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Message_errorName_x3f(v_msg_2794_);
lean_dec_ref(v_msg_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2796_){
_start:
{
lean_object* v_toBaseMessage_2797_; lean_object* v_fileName_2798_; lean_object* v_pos_2799_; lean_object* v_endPos_2800_; uint8_t v_keepFullRange_2801_; uint8_t v_severity_2802_; uint8_t v_isSilent_2803_; lean_object* v_caption_2804_; lean_object* v_data_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2814_; 
v_toBaseMessage_2797_ = lean_ctor_get(v_msg_2796_, 0);
lean_inc_ref(v_toBaseMessage_2797_);
lean_dec_ref(v_msg_2796_);
v_fileName_2798_ = lean_ctor_get(v_toBaseMessage_2797_, 0);
v_pos_2799_ = lean_ctor_get(v_toBaseMessage_2797_, 1);
v_endPos_2800_ = lean_ctor_get(v_toBaseMessage_2797_, 2);
v_keepFullRange_2801_ = lean_ctor_get_uint8(v_toBaseMessage_2797_, sizeof(void*)*5);
v_severity_2802_ = lean_ctor_get_uint8(v_toBaseMessage_2797_, sizeof(void*)*5 + 1);
v_isSilent_2803_ = lean_ctor_get_uint8(v_toBaseMessage_2797_, sizeof(void*)*5 + 2);
v_caption_2804_ = lean_ctor_get(v_toBaseMessage_2797_, 3);
v_data_2805_ = lean_ctor_get(v_toBaseMessage_2797_, 4);
v_isSharedCheck_2814_ = !lean_is_exclusive(v_toBaseMessage_2797_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2807_ = v_toBaseMessage_2797_;
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_data_2805_);
lean_inc(v_caption_2804_);
lean_inc(v_endPos_2800_);
lean_inc(v_pos_2799_);
lean_inc(v_fileName_2798_);
lean_dec(v_toBaseMessage_2797_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2814_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2809_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2809_, 0, v_data_2805_);
v___x_2810_ = l_Lean_MessageData_ofFormat(v___x_2809_);
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 4, v___x_2810_);
v___x_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_fileName_2798_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v_pos_2799_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v_endPos_2800_);
lean_ctor_set(v_reuseFailAlloc_2813_, 3, v_caption_2804_);
lean_ctor_set(v_reuseFailAlloc_2813_, 4, v___x_2810_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, sizeof(void*)*5, v_keepFullRange_2801_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, sizeof(void*)*5 + 1, v_severity_2802_);
lean_ctor_set_uint8(v_reuseFailAlloc_2813_, sizeof(void*)*5 + 2, v_isSilent_2803_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2820_, uint8_t v_includeEndPos_2821_){
_start:
{
lean_object* v___y_2823_; lean_object* v___y_2827_; uint32_t v___y_2828_; lean_object* v___y_2832_; lean_object* v_str_2835_; lean_object* v_toBaseMessage_2845_; lean_object* v_kind_2846_; lean_object* v_fileName_2847_; lean_object* v_pos_2848_; lean_object* v_endPos_2849_; uint8_t v_severity_2850_; lean_object* v_caption_2851_; lean_object* v_data_2852_; lean_object* v___y_2854_; lean_object* v_str_2855_; lean_object* v___y_2863_; 
v_toBaseMessage_2845_ = lean_ctor_get(v_msg_2820_, 0);
lean_inc_ref(v_toBaseMessage_2845_);
v_kind_2846_ = lean_ctor_get(v_msg_2820_, 1);
lean_inc(v_kind_2846_);
lean_dec_ref(v_msg_2820_);
v_fileName_2847_ = lean_ctor_get(v_toBaseMessage_2845_, 0);
lean_inc_ref(v_fileName_2847_);
v_pos_2848_ = lean_ctor_get(v_toBaseMessage_2845_, 1);
lean_inc_ref(v_pos_2848_);
v_endPos_2849_ = lean_ctor_get(v_toBaseMessage_2845_, 2);
lean_inc(v_endPos_2849_);
v_severity_2850_ = lean_ctor_get_uint8(v_toBaseMessage_2845_, sizeof(void*)*5 + 1);
v_caption_2851_ = lean_ctor_get(v_toBaseMessage_2845_, 3);
lean_inc_ref(v_caption_2851_);
v_data_2852_ = lean_ctor_get(v_toBaseMessage_2845_, 4);
lean_inc(v_data_2852_);
lean_dec_ref(v_toBaseMessage_2845_);
if (v_includeEndPos_2821_ == 0)
{
lean_object* v___x_2869_; 
lean_dec(v_endPos_2849_);
v___x_2869_ = lean_box(0);
v___y_2863_ = v___x_2869_;
goto v___jp_2862_;
}
else
{
v___y_2863_ = v_endPos_2849_;
goto v___jp_2862_;
}
v___jp_2822_:
{
lean_object* v___x_2824_; lean_object* v_str_2825_; 
v___x_2824_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2825_ = lean_string_append(v___y_2823_, v___x_2824_);
return v_str_2825_;
}
v___jp_2826_:
{
uint32_t v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = 10;
v___x_2830_ = lean_uint32_dec_eq(v___y_2828_, v___x_2829_);
if (v___x_2830_ == 0)
{
v___y_2823_ = v___y_2827_;
goto v___jp_2822_;
}
else
{
return v___y_2827_;
}
}
v___jp_2831_:
{
uint32_t v___x_2833_; 
v___x_2833_ = 65;
v___y_2827_ = v___y_2832_;
v___y_2828_ = v___x_2833_;
goto v___jp_2826_;
}
v___jp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v___x_2836_ = lean_string_utf8_byte_size(v_str_2835_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = lean_nat_dec_eq(v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
lean_inc_ref(v_str_2835_);
v___x_2839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2839_, 0, v_str_2835_);
lean_ctor_set(v___x_2839_, 1, v___x_2837_);
lean_ctor_set(v___x_2839_, 2, v___x_2836_);
v___x_2840_ = l_String_Slice_Pos_prev_x3f(v___x_2839_, v___x_2836_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_dec_ref_known(v___x_2839_, 3);
v___y_2832_ = v_str_2835_;
goto v___jp_2831_;
}
else
{
lean_object* v_val_2841_; lean_object* v___x_2842_; 
v_val_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_val_2841_);
lean_dec_ref_known(v___x_2840_, 1);
v___x_2842_ = l_String_Slice_Pos_get_x3f(v___x_2839_, v_val_2841_);
lean_dec(v_val_2841_);
lean_dec_ref_known(v___x_2839_, 3);
if (lean_obj_tag(v___x_2842_) == 0)
{
v___y_2832_ = v_str_2835_;
goto v___jp_2831_;
}
else
{
lean_object* v_val_2843_; uint32_t v___x_2844_; 
v_val_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v___x_2842_, 1);
v___x_2844_ = lean_unbox_uint32(v_val_2843_);
lean_dec(v_val_2843_);
v___y_2827_ = v_str_2835_;
v___y_2828_ = v___x_2844_;
goto v___jp_2826_;
}
}
}
else
{
v___y_2823_ = v_str_2835_;
goto v___jp_2822_;
}
}
v___jp_2853_:
{
switch(v_severity_2850_)
{
case 0:
{
lean_dec(v___y_2854_);
lean_dec_ref(v_pos_2848_);
lean_dec_ref(v_fileName_2847_);
lean_dec(v_kind_2846_);
v_str_2835_ = v_str_2855_;
goto v___jp_2834_;
}
case 1:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v_str_2858_; 
v___x_2856_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2857_ = l_Lean_errorNameOfKind_x3f(v_kind_2846_);
lean_dec(v_kind_2846_);
v_str_2858_ = l_Lean_mkErrorStringWithPos(v_fileName_2847_, v_pos_2848_, v_str_2855_, v___y_2854_, v___x_2856_, v___x_2857_);
lean_dec_ref(v_str_2855_);
v_str_2835_ = v_str_2858_;
goto v___jp_2834_;
}
default: 
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_str_2861_; 
v___x_2859_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2860_ = l_Lean_errorNameOfKind_x3f(v_kind_2846_);
lean_dec(v_kind_2846_);
v_str_2861_ = l_Lean_mkErrorStringWithPos(v_fileName_2847_, v_pos_2848_, v_str_2855_, v___y_2854_, v___x_2859_, v___x_2860_);
lean_dec_ref(v_str_2855_);
v_str_2835_ = v_str_2861_;
goto v___jp_2834_;
}
}
}
v___jp_2862_:
{
lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2864_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2865_ = lean_string_dec_eq(v_caption_2851_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_str_2868_; 
v___x_2866_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2867_ = lean_string_append(v_caption_2851_, v___x_2866_);
v_str_2868_ = lean_string_append(v___x_2867_, v_data_2852_);
lean_dec(v_data_2852_);
v___y_2854_ = v___y_2863_;
v_str_2855_ = v_str_2868_;
goto v___jp_2853_;
}
else
{
lean_dec_ref(v_caption_2851_);
v___y_2854_ = v___y_2863_;
v_str_2855_ = v_data_2852_;
goto v___jp_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_2870_, lean_object* v_includeEndPos_2871_){
_start:
{
uint8_t v_includeEndPos_boxed_2872_; lean_object* v_res_2873_; 
v_includeEndPos_boxed_2872_ = lean_unbox(v_includeEndPos_2871_);
v_res_2873_ = l_Lean_SerialMessage_toString(v_msg_2870_, v_includeEndPos_boxed_2872_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_2874_){
_start:
{
uint8_t v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = 0;
v___x_2876_ = l_Lean_SerialMessage_toString(v_msg_2874_, v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_2879_){
_start:
{
lean_object* v_data_2880_; lean_object* v___x_2881_; 
v_data_2880_ = lean_ctor_get(v_msg_2879_, 4);
v___x_2881_ = l_Lean_MessageData_kind(v_data_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_Lean_Message_kind(v_msg_2882_);
lean_dec_ref(v_msg_2882_);
return v_res_2883_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_2884_){
_start:
{
lean_object* v_data_2885_; uint8_t v___x_2886_; 
v_data_2885_ = lean_ctor_get(v_msg_2884_, 4);
v___x_2886_ = l_Lean_MessageData_isTrace(v_data_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_Lean_Message_isTrace(v_msg_2887_);
lean_dec_ref(v_msg_2887_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_2890_){
_start:
{
lean_object* v_fileName_2892_; lean_object* v_pos_2893_; lean_object* v_endPos_2894_; uint8_t v_keepFullRange_2895_; uint8_t v_severity_2896_; uint8_t v_isSilent_2897_; lean_object* v_caption_2898_; lean_object* v_data_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2909_; 
v_fileName_2892_ = lean_ctor_get(v_msg_2890_, 0);
v_pos_2893_ = lean_ctor_get(v_msg_2890_, 1);
v_endPos_2894_ = lean_ctor_get(v_msg_2890_, 2);
v_keepFullRange_2895_ = lean_ctor_get_uint8(v_msg_2890_, sizeof(void*)*5);
v_severity_2896_ = lean_ctor_get_uint8(v_msg_2890_, sizeof(void*)*5 + 1);
v_isSilent_2897_ = lean_ctor_get_uint8(v_msg_2890_, sizeof(void*)*5 + 2);
v_caption_2898_ = lean_ctor_get(v_msg_2890_, 3);
v_data_2899_ = lean_ctor_get(v_msg_2890_, 4);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_msg_2890_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2901_ = v_msg_2890_;
v_isShared_2902_ = v_isSharedCheck_2909_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_data_2899_);
lean_inc(v_caption_2898_);
lean_inc(v_endPos_2894_);
lean_inc(v_pos_2893_);
lean_inc(v_fileName_2892_);
lean_dec(v_msg_2890_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2909_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
lean_inc(v_data_2899_);
v___x_2903_ = l_Lean_MessageData_toString(v_data_2899_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 4, v___x_2903_);
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_fileName_2892_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_pos_2893_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v_endPos_2894_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v_caption_2898_);
lean_ctor_set(v_reuseFailAlloc_2908_, 4, v___x_2903_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*5, v_keepFullRange_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*5 + 1, v_severity_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2908_, sizeof(void*)*5 + 2, v_isSilent_2897_);
v___x_2905_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = l_Lean_MessageData_kind(v_data_2899_);
lean_dec(v_data_2899_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
return v___x_2907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Message_serialize(v_msg_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_2913_, uint8_t v_includeEndPos_2914_){
_start:
{
lean_object* v_fileName_2916_; lean_object* v_pos_2917_; lean_object* v_endPos_2918_; uint8_t v_severity_2919_; lean_object* v_caption_2920_; lean_object* v_data_2921_; lean_object* v___x_2922_; lean_object* v___y_2924_; lean_object* v___y_2928_; uint32_t v___y_2929_; lean_object* v___y_2933_; lean_object* v_str_2936_; lean_object* v___x_2946_; lean_object* v___y_2948_; lean_object* v_str_2949_; lean_object* v___y_2957_; 
v_fileName_2916_ = lean_ctor_get(v_msg_2913_, 0);
lean_inc_ref(v_fileName_2916_);
v_pos_2917_ = lean_ctor_get(v_msg_2913_, 1);
lean_inc_ref(v_pos_2917_);
v_endPos_2918_ = lean_ctor_get(v_msg_2913_, 2);
lean_inc(v_endPos_2918_);
v_severity_2919_ = lean_ctor_get_uint8(v_msg_2913_, sizeof(void*)*5 + 1);
v_caption_2920_ = lean_ctor_get(v_msg_2913_, 3);
lean_inc_ref(v_caption_2920_);
v_data_2921_ = lean_ctor_get(v_msg_2913_, 4);
lean_inc_n(v_data_2921_, 2);
lean_dec_ref(v_msg_2913_);
v___x_2922_ = l_Lean_MessageData_toString(v_data_2921_);
v___x_2946_ = l_Lean_MessageData_kind(v_data_2921_);
lean_dec(v_data_2921_);
if (v_includeEndPos_2914_ == 0)
{
lean_object* v___x_2963_; 
lean_dec(v_endPos_2918_);
v___x_2963_ = lean_box(0);
v___y_2957_ = v___x_2963_;
goto v___jp_2956_;
}
else
{
v___y_2957_ = v_endPos_2918_;
goto v___jp_2956_;
}
v___jp_2923_:
{
lean_object* v___x_2925_; lean_object* v_str_2926_; 
v___x_2925_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2926_ = lean_string_append(v___y_2924_, v___x_2925_);
return v_str_2926_;
}
v___jp_2927_:
{
uint32_t v___x_2930_; uint8_t v___x_2931_; 
v___x_2930_ = 10;
v___x_2931_ = lean_uint32_dec_eq(v___y_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
v___y_2924_ = v___y_2928_;
goto v___jp_2923_;
}
else
{
return v___y_2928_;
}
}
v___jp_2932_:
{
uint32_t v___x_2934_; 
v___x_2934_ = 65;
v___y_2928_ = v___y_2933_;
v___y_2929_ = v___x_2934_;
goto v___jp_2927_;
}
v___jp_2935_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2937_ = lean_string_utf8_byte_size(v_str_2936_);
v___x_2938_ = lean_unsigned_to_nat(0u);
v___x_2939_ = lean_nat_dec_eq(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_inc_ref(v_str_2936_);
v___x_2940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2940_, 0, v_str_2936_);
lean_ctor_set(v___x_2940_, 1, v___x_2938_);
lean_ctor_set(v___x_2940_, 2, v___x_2937_);
v___x_2941_ = l_String_Slice_Pos_prev_x3f(v___x_2940_, v___x_2937_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_dec_ref_known(v___x_2940_, 3);
v___y_2933_ = v_str_2936_;
goto v___jp_2932_;
}
else
{
lean_object* v_val_2942_; lean_object* v___x_2943_; 
v_val_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_val_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = l_String_Slice_Pos_get_x3f(v___x_2940_, v_val_2942_);
lean_dec(v_val_2942_);
lean_dec_ref_known(v___x_2940_, 3);
if (lean_obj_tag(v___x_2943_) == 0)
{
v___y_2933_ = v_str_2936_;
goto v___jp_2932_;
}
else
{
lean_object* v_val_2944_; uint32_t v___x_2945_; 
v_val_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_val_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = lean_unbox_uint32(v_val_2944_);
lean_dec(v_val_2944_);
v___y_2928_ = v_str_2936_;
v___y_2929_ = v___x_2945_;
goto v___jp_2927_;
}
}
}
else
{
v___y_2924_ = v_str_2936_;
goto v___jp_2923_;
}
}
v___jp_2947_:
{
switch(v_severity_2919_)
{
case 0:
{
lean_dec(v___y_2948_);
lean_dec(v___x_2946_);
lean_dec_ref(v_pos_2917_);
lean_dec_ref(v_fileName_2916_);
v_str_2936_ = v_str_2949_;
goto v___jp_2935_;
}
case 1:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_str_2952_; 
v___x_2950_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2951_ = l_Lean_errorNameOfKind_x3f(v___x_2946_);
lean_dec(v___x_2946_);
v_str_2952_ = l_Lean_mkErrorStringWithPos(v_fileName_2916_, v_pos_2917_, v_str_2949_, v___y_2948_, v___x_2950_, v___x_2951_);
lean_dec_ref(v_str_2949_);
v_str_2936_ = v_str_2952_;
goto v___jp_2935_;
}
default: 
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_str_2955_; 
v___x_2953_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2954_ = l_Lean_errorNameOfKind_x3f(v___x_2946_);
lean_dec(v___x_2946_);
v_str_2955_ = l_Lean_mkErrorStringWithPos(v_fileName_2916_, v_pos_2917_, v_str_2949_, v___y_2948_, v___x_2953_, v___x_2954_);
lean_dec_ref(v_str_2949_);
v_str_2936_ = v_str_2955_;
goto v___jp_2935_;
}
}
}
v___jp_2956_:
{
lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2959_ = lean_string_dec_eq(v_caption_2920_, v___x_2958_);
if (v___x_2959_ == 0)
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_str_2962_; 
v___x_2960_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_2961_ = lean_string_append(v_caption_2920_, v___x_2960_);
v_str_2962_ = lean_string_append(v___x_2961_, v___x_2922_);
lean_dec_ref(v___x_2922_);
v___y_2948_ = v___y_2957_;
v_str_2949_ = v_str_2962_;
goto v___jp_2947_;
}
else
{
lean_dec_ref(v_caption_2920_);
v___y_2948_ = v___y_2957_;
v_str_2949_ = v___x_2922_;
goto v___jp_2947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_2964_, lean_object* v_includeEndPos_2965_, lean_object* v_a_2966_){
_start:
{
uint8_t v_includeEndPos_boxed_2967_; lean_object* v_res_2968_; 
v_includeEndPos_boxed_2967_ = lean_unbox(v_includeEndPos_2965_);
v_res_2968_ = l_Lean_Message_toString(v_msg_2964_, v_includeEndPos_boxed_2967_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_2969_){
_start:
{
lean_object* v_fileName_2971_; lean_object* v_pos_2972_; lean_object* v_endPos_2973_; uint8_t v_keepFullRange_2974_; uint8_t v_severity_2975_; uint8_t v_isSilent_2976_; lean_object* v_caption_2977_; lean_object* v_data_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_fileName_2971_ = lean_ctor_get(v_msg_2969_, 0);
lean_inc_ref(v_fileName_2971_);
v_pos_2972_ = lean_ctor_get(v_msg_2969_, 1);
lean_inc_ref(v_pos_2972_);
v_endPos_2973_ = lean_ctor_get(v_msg_2969_, 2);
lean_inc(v_endPos_2973_);
v_keepFullRange_2974_ = lean_ctor_get_uint8(v_msg_2969_, sizeof(void*)*5);
v_severity_2975_ = lean_ctor_get_uint8(v_msg_2969_, sizeof(void*)*5 + 1);
v_isSilent_2976_ = lean_ctor_get_uint8(v_msg_2969_, sizeof(void*)*5 + 2);
v_caption_2977_ = lean_ctor_get(v_msg_2969_, 3);
lean_inc_ref(v_caption_2977_);
v_data_2978_ = lean_ctor_get(v_msg_2969_, 4);
lean_inc_n(v_data_2978_, 2);
lean_dec_ref(v_msg_2969_);
v___x_2979_ = l_Lean_MessageData_toString(v_data_2978_);
v___x_2980_ = l_Lean_MessageData_kind(v_data_2978_);
lean_dec(v_data_2978_);
v___x_2981_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_fileName_2971_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2981_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2983_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2987_ = l_Lean_instToJsonPosition_toJson(v_pos_2972_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
lean_ctor_set(v___x_2989_, 1, v___x_2984_);
v___x_2990_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2991_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2973_);
v___x_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2990_);
lean_ctor_set(v___x_2992_, 1, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v___x_2984_);
v___x_2994_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2995_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2995_, 0, v_keepFullRange_2974_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2994_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2997_, 0, v___x_2996_);
lean_ctor_set(v___x_2997_, 1, v___x_2984_);
v___x_2998_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2999_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2975_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2998_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2984_);
v___x_3002_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3003_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3003_, 0, v_isSilent_2976_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3002_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
lean_ctor_set(v___x_3005_, 1, v___x_2984_);
v___x_3006_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_caption_2977_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v___x_2984_);
v___x_3010_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_2979_);
v___x_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3010_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_2984_);
v___x_3014_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3015_ = 1;
v___x_3016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2980_, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3014_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_2984_);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v___x_2984_);
v___x_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3013_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3009_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3005_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3001_);
lean_ctor_set(v___x_3024_, 1, v___x_3023_);
v___x_3025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_2997_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_2993_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_2989_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_2985_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3030_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3028_, v___x_3029_);
v___x_3031_ = l_Lean_Json_mkObj(v___x_3030_);
lean_dec(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Message_toJson(v_msg_3032_);
return v_res_3034_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_unsigned_to_nat(32u);
v___x_3036_ = lean_mk_empty_array_with_capacity(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3038_ = ((size_t)5ULL);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_unsigned_to_nat(32u);
v___x_3041_ = lean_mk_empty_array_with_capacity(v___x_3040_);
v___x_3042_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3043_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3041_);
lean_ctor_set(v___x_3043_, 2, v___x_3039_);
lean_ctor_set(v___x_3043_, 3, v___x_3039_);
lean_ctor_set_usize(v___x_3043_, 4, v___x_3038_);
return v___x_3043_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = l_Lean_NameSet_empty;
v___x_3045_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
lean_ctor_set(v___x_3046_, 2, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3048_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = lean_unsigned_to_nat(32u);
v___x_3050_ = lean_mk_empty_array_with_capacity(v___x_3049_);
lean_dec_ref(v___x_3050_);
v___x_3051_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3052_){
_start:
{
lean_object* v_unreported_3053_; 
v_unreported_3053_ = lean_ctor_get(v_self_3052_, 1);
lean_inc_ref(v_unreported_3053_);
return v_unreported_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_MessageLog_msgs(v_self_3054_);
lean_dec_ref(v_self_3054_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3056_){
_start:
{
lean_object* v_reported_3057_; lean_object* v_unreported_3058_; lean_object* v___x_3059_; 
v_reported_3057_ = lean_ctor_get(v_x_3056_, 0);
lean_inc_ref(v_reported_3057_);
v_unreported_3058_ = lean_ctor_get(v_x_3056_, 1);
lean_inc_ref(v_unreported_3058_);
lean_dec_ref(v_x_3056_);
v___x_3059_ = l_Lean_PersistentArray_append___redArg(v_reported_3057_, v_unreported_3058_);
lean_dec_ref(v_unreported_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3060_){
_start:
{
lean_object* v_unreported_3061_; uint8_t v___x_3062_; 
v_unreported_3061_ = lean_ctor_get(v_log_3060_, 1);
v___x_3062_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3061_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
v___x_3063_ = 1;
return v___x_3063_;
}
else
{
uint8_t v___x_3064_; 
v___x_3064_ = 0;
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3065_){
_start:
{
uint8_t v_res_3066_; lean_object* v_r_3067_; 
v_res_3066_ = l_Lean_MessageLog_hasUnreported(v_log_3065_);
lean_dec_ref(v_log_3065_);
v_r_3067_ = lean_box(v_res_3066_);
return v_r_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3068_, lean_object* v_log_3069_){
_start:
{
lean_object* v_reported_3070_; lean_object* v_unreported_3071_; lean_object* v_loggedKinds_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3080_; 
v_reported_3070_ = lean_ctor_get(v_log_3069_, 0);
v_unreported_3071_ = lean_ctor_get(v_log_3069_, 1);
v_loggedKinds_3072_ = lean_ctor_get(v_log_3069_, 2);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_log_3069_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3074_ = v_log_3069_;
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_loggedKinds_3072_);
lean_inc(v_unreported_3071_);
lean_inc(v_reported_3070_);
lean_dec(v_log_3069_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3080_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = l_Lean_PersistentArray_push___redArg(v_unreported_3071_, v_msg_3068_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v___x_3076_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_reported_3070_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_loggedKinds_3072_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3085_, 0, v_b_u2082_3083_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3087_, lean_object* v_x_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3087_, v_x_3088_);
lean_dec(v_x_3088_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3090_, lean_object* v_k_3091_, lean_object* v_t_3092_){
_start:
{
if (lean_obj_tag(v_t_3092_) == 0)
{
lean_object* v_size_3093_; lean_object* v_k_3094_; lean_object* v_v_3095_; lean_object* v_l_3096_; lean_object* v_r_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3112_; 
v_size_3093_ = lean_ctor_get(v_t_3092_, 0);
v_k_3094_ = lean_ctor_get(v_t_3092_, 1);
v_v_3095_ = lean_ctor_get(v_t_3092_, 2);
v_l_3096_ = lean_ctor_get(v_t_3092_, 3);
v_r_3097_ = lean_ctor_get(v_t_3092_, 4);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_t_3092_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3099_ = v_t_3092_;
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_r_3097_);
lean_inc(v_l_3096_);
lean_inc(v_v_3095_);
lean_inc(v_k_3094_);
lean_inc(v_size_3093_);
lean_dec(v_t_3092_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
uint8_t v___x_3101_; 
v___x_3101_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3091_, v_k_3094_);
switch(v___x_3101_)
{
case 0:
{
lean_object* v_impl_3102_; lean_object* v___x_3103_; 
lean_del_object(v___x_3099_);
lean_dec(v_size_3093_);
v_impl_3102_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3090_, v_k_3091_, v_l_3096_);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3094_, v_v_3095_, v_impl_3102_, v_r_3097_);
return v___x_3103_;
}
case 1:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v_val_3106_; lean_object* v___x_3108_; 
lean_dec(v_k_3094_);
v___x_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3104_, 0, v_v_3095_);
v___x_3105_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3090_, v___x_3104_);
lean_dec_ref_known(v___x_3104_, 1);
v_val_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_val_3106_);
lean_dec(v___x_3105_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 2, v_val_3106_);
lean_ctor_set(v___x_3099_, 1, v_k_3091_);
v___x_3108_ = v___x_3099_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_size_3093_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_k_3091_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_val_3106_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_l_3096_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_r_3097_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
default: 
{
lean_object* v_impl_3110_; lean_object* v___x_3111_; 
lean_del_object(v___x_3099_);
lean_dec(v_size_3093_);
v_impl_3110_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3090_, v_k_3091_, v_r_3097_);
v___x_3111_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3094_, v_v_3095_, v_l_3096_, v_impl_3110_);
return v___x_3111_;
}
}
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v_val_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3113_ = lean_box(0);
v___x_3114_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3090_, v___x_3113_);
v_val_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3115_);
lean_dec(v___x_3114_);
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v_k_3091_);
lean_ctor_set(v___x_3117_, 2, v_val_3115_);
lean_ctor_set(v___x_3117_, 3, v_t_3092_);
lean_ctor_set(v___x_3117_, 4, v_t_3092_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3118_, lean_object* v_x_3119_){
_start:
{
if (lean_obj_tag(v_x_3119_) == 0)
{
lean_object* v_k_3120_; lean_object* v_v_3121_; lean_object* v_l_3122_; lean_object* v_r_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_k_3120_ = lean_ctor_get(v_x_3119_, 1);
lean_inc(v_k_3120_);
v_v_3121_ = lean_ctor_get(v_x_3119_, 2);
lean_inc(v_v_3121_);
v_l_3122_ = lean_ctor_get(v_x_3119_, 3);
lean_inc(v_l_3122_);
v_r_3123_ = lean_ctor_get(v_x_3119_, 4);
lean_inc(v_r_3123_);
lean_dec_ref_known(v_x_3119_, 5);
v___x_3124_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3118_, v_l_3122_);
v___x_3125_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3121_, v_k_3120_, v___x_3124_);
v_init_3118_ = v___x_3125_;
v_x_3119_ = v_r_3123_;
goto _start;
}
else
{
return v_init_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3127_, lean_object* v_l_u2082_3128_){
_start:
{
lean_object* v_reported_3129_; lean_object* v_unreported_3130_; lean_object* v_loggedKinds_3131_; lean_object* v_reported_3132_; lean_object* v_unreported_3133_; lean_object* v_loggedKinds_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3144_; 
v_reported_3129_ = lean_ctor_get(v_l_u2081_3127_, 0);
lean_inc_ref(v_reported_3129_);
v_unreported_3130_ = lean_ctor_get(v_l_u2081_3127_, 1);
lean_inc_ref(v_unreported_3130_);
v_loggedKinds_3131_ = lean_ctor_get(v_l_u2081_3127_, 2);
lean_inc(v_loggedKinds_3131_);
lean_dec_ref(v_l_u2081_3127_);
v_reported_3132_ = lean_ctor_get(v_l_u2082_3128_, 0);
v_unreported_3133_ = lean_ctor_get(v_l_u2082_3128_, 1);
v_loggedKinds_3134_ = lean_ctor_get(v_l_u2082_3128_, 2);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_l_u2082_3128_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3136_ = v_l_u2082_3128_;
v_isShared_3137_ = v_isSharedCheck_3144_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_loggedKinds_3134_);
lean_inc(v_unreported_3133_);
lean_inc(v_reported_3132_);
lean_dec(v_l_u2082_3128_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3144_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3138_ = l_Lean_PersistentArray_append___redArg(v_reported_3129_, v_reported_3132_);
lean_dec_ref(v_reported_3132_);
v___x_3139_ = l_Lean_PersistentArray_append___redArg(v_unreported_3130_, v_unreported_3133_);
lean_dec_ref(v_unreported_3133_);
v___x_3140_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3131_, v_loggedKinds_3134_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 2, v___x_3140_);
lean_ctor_set(v___x_3136_, 1, v___x_3139_);
lean_ctor_set(v___x_3136_, 0, v___x_3138_);
v___x_3142_ = v___x_3136_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3145_, lean_object* v_k_3146_, lean_object* v_t_3147_, lean_object* v_hl_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3145_, v_k_3146_, v_t_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3150_, lean_object* v_t_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3150_, v_t_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_eq(v_i_3156_, v_stop_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; uint8_t v_severity_3160_; 
v___x_3159_ = lean_array_uget_borrowed(v_as_3155_, v_i_3156_);
v_severity_3160_ = lean_ctor_get_uint8(v___x_3159_, sizeof(void*)*5 + 1);
if (v_severity_3160_ == 2)
{
uint8_t v___x_3161_; 
v___x_3161_ = 1;
return v___x_3161_;
}
else
{
size_t v___x_3162_; size_t v___x_3163_; 
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3156_, v___x_3162_);
v_i_3156_ = v___x_3163_;
goto _start;
}
}
else
{
uint8_t v___x_3165_; 
v___x_3165_ = 0;
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3166_, lean_object* v_i_3167_, lean_object* v_stop_3168_){
_start:
{
size_t v_i_boxed_3169_; size_t v_stop_boxed_3170_; uint8_t v_res_3171_; lean_object* v_r_3172_; 
v_i_boxed_3169_ = lean_unbox_usize(v_i_3167_);
lean_dec(v_i_3167_);
v_stop_boxed_3170_ = lean_unbox_usize(v_stop_3168_);
lean_dec(v_stop_3168_);
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3166_, v_i_boxed_3169_, v_stop_boxed_3170_);
lean_dec_ref(v_as_3166_);
v_r_3172_ = lean_box(v_res_3171_);
return v_r_3172_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
lean_object* v_cs_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_cs_3174_ = lean_ctor_get(v_x_3173_, 0);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = lean_array_get_size(v_cs_3174_);
v___x_3177_ = lean_nat_dec_lt(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
return v___x_3177_;
}
else
{
size_t v___x_3178_; size_t v___x_3179_; uint8_t v___x_3180_; 
v___x_3178_ = ((size_t)0ULL);
v___x_3179_ = lean_usize_of_nat(v___x_3176_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3174_, v___x_3178_, v___x_3179_);
return v___x_3180_;
}
}
else
{
lean_object* v_vs_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_vs_3181_ = lean_ctor_get(v_x_3173_, 0);
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_array_get_size(v_vs_3181_);
v___x_3184_ = lean_nat_dec_lt(v___x_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
return v___x_3184_;
}
else
{
size_t v___x_3185_; size_t v___x_3186_; uint8_t v___x_3187_; 
v___x_3185_ = ((size_t)0ULL);
v___x_3186_ = lean_usize_of_nat(v___x_3183_);
v___x_3187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3181_, v___x_3185_, v___x_3186_);
return v___x_3187_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3188_, size_t v_i_3189_, size_t v_stop_3190_){
_start:
{
uint8_t v___x_3191_; 
v___x_3191_ = lean_usize_dec_eq(v_i_3189_, v_stop_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = lean_array_uget_borrowed(v_as_3188_, v_i_3189_);
v___x_3193_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3192_);
if (v___x_3193_ == 0)
{
size_t v___x_3194_; size_t v___x_3195_; 
v___x_3194_ = ((size_t)1ULL);
v___x_3195_ = lean_usize_add(v_i_3189_, v___x_3194_);
v_i_3189_ = v___x_3195_;
goto _start;
}
else
{
return v___x_3193_;
}
}
else
{
uint8_t v___x_3197_; 
v___x_3197_ = 0;
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3198_, lean_object* v_i_3199_, lean_object* v_stop_3200_){
_start:
{
size_t v_i_boxed_3201_; size_t v_stop_boxed_3202_; uint8_t v_res_3203_; lean_object* v_r_3204_; 
v_i_boxed_3201_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_stop_boxed_3202_ = lean_unbox_usize(v_stop_3200_);
lean_dec(v_stop_3200_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3198_, v_i_boxed_3201_, v_stop_boxed_3202_);
lean_dec_ref(v_as_3198_);
v_r_3204_ = lean_box(v_res_3203_);
return v_r_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3205_){
_start:
{
uint8_t v_res_3206_; lean_object* v_r_3207_; 
v_res_3206_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3205_);
lean_dec_ref(v_x_3205_);
v_r_3207_ = lean_box(v_res_3206_);
return v_r_3207_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3208_){
_start:
{
lean_object* v_root_3209_; lean_object* v_tail_3210_; uint8_t v___x_3211_; 
v_root_3209_ = lean_ctor_get(v_t_3208_, 0);
v_tail_3210_ = lean_ctor_get(v_t_3208_, 1);
v___x_3211_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3209_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = lean_array_get_size(v_tail_3210_);
v___x_3214_ = lean_nat_dec_lt(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
return v___x_3214_;
}
else
{
size_t v___x_3215_; size_t v___x_3216_; uint8_t v___x_3217_; 
v___x_3215_ = ((size_t)0ULL);
v___x_3216_ = lean_usize_of_nat(v___x_3213_);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3210_, v___x_3215_, v___x_3216_);
return v___x_3217_;
}
}
else
{
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3218_){
_start:
{
uint8_t v_res_3219_; lean_object* v_r_3220_; 
v_res_3219_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3218_);
lean_dec_ref(v_t_3218_);
v_r_3220_ = lean_box(v_res_3219_);
return v_r_3220_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3221_, lean_object* v_as_3222_, size_t v_i_3223_, size_t v_stop_3224_){
_start:
{
uint8_t v___x_3225_; 
v___x_3225_ = lean_usize_dec_eq(v_i_3223_, v_stop_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; uint8_t v_severity_3227_; uint8_t v___x_3228_; 
v___x_3226_ = lean_array_uget_borrowed(v_as_3222_, v_i_3223_);
v_severity_3227_ = lean_ctor_get_uint8(v___x_3226_, sizeof(void*)*5 + 1);
v___x_3228_ = 1;
if (v_severity_3227_ == 2)
{
return v___x_3228_;
}
else
{
if (v___x_3221_ == 0)
{
size_t v___x_3229_; size_t v___x_3230_; 
v___x_3229_ = ((size_t)1ULL);
v___x_3230_ = lean_usize_add(v_i_3223_, v___x_3229_);
v_i_3223_ = v___x_3230_;
goto _start;
}
else
{
return v___x_3228_;
}
}
}
else
{
uint8_t v___x_3232_; 
v___x_3232_ = 0;
return v___x_3232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3233_, lean_object* v_as_3234_, lean_object* v_i_3235_, lean_object* v_stop_3236_){
_start:
{
uint8_t v___x_1809__boxed_3237_; size_t v_i_boxed_3238_; size_t v_stop_boxed_3239_; uint8_t v_res_3240_; lean_object* v_r_3241_; 
v___x_1809__boxed_3237_ = lean_unbox(v___x_3233_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_stop_boxed_3239_ = lean_unbox_usize(v_stop_3236_);
lean_dec(v_stop_3236_);
v_res_3240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3237_, v_as_3234_, v_i_boxed_3238_, v_stop_boxed_3239_);
lean_dec_ref(v_as_3234_);
v_r_3241_ = lean_box(v_res_3240_);
return v_r_3241_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3242_, lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3243_) == 0)
{
lean_object* v_cs_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_cs_3244_ = lean_ctor_get(v_x_3243_, 0);
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = lean_array_get_size(v_cs_3244_);
v___x_3247_ = lean_nat_dec_lt(v___x_3245_, v___x_3246_);
if (v___x_3247_ == 0)
{
return v___x_3247_;
}
else
{
size_t v___x_3248_; size_t v___x_3249_; uint8_t v___x_3250_; 
v___x_3248_ = ((size_t)0ULL);
v___x_3249_ = lean_usize_of_nat(v___x_3246_);
v___x_3250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3242_, v_cs_3244_, v___x_3248_, v___x_3249_);
return v___x_3250_;
}
}
else
{
lean_object* v_vs_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; uint8_t v___x_3254_; 
v_vs_3251_ = lean_ctor_get(v_x_3243_, 0);
v___x_3252_ = lean_unsigned_to_nat(0u);
v___x_3253_ = lean_array_get_size(v_vs_3251_);
v___x_3254_ = lean_nat_dec_lt(v___x_3252_, v___x_3253_);
if (v___x_3254_ == 0)
{
return v___x_3254_;
}
else
{
size_t v___x_3255_; size_t v___x_3256_; uint8_t v___x_3257_; 
v___x_3255_ = ((size_t)0ULL);
v___x_3256_ = lean_usize_of_nat(v___x_3253_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3242_, v_vs_3251_, v___x_3255_, v___x_3256_);
return v___x_3257_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3258_, lean_object* v_as_3259_, size_t v_i_3260_, size_t v_stop_3261_){
_start:
{
uint8_t v___x_3262_; 
v___x_3262_ = lean_usize_dec_eq(v_i_3260_, v_stop_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_array_uget_borrowed(v_as_3259_, v_i_3260_);
v___x_3264_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3258_, v___x_3263_);
if (v___x_3264_ == 0)
{
size_t v___x_3265_; size_t v___x_3266_; 
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3260_, v___x_3265_);
v_i_3260_ = v___x_3266_;
goto _start;
}
else
{
return v___x_3264_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3269_, lean_object* v_as_3270_, lean_object* v_i_3271_, lean_object* v_stop_3272_){
_start:
{
uint8_t v___x_1826__boxed_3273_; size_t v_i_boxed_3274_; size_t v_stop_boxed_3275_; uint8_t v_res_3276_; lean_object* v_r_3277_; 
v___x_1826__boxed_3273_ = lean_unbox(v___x_3269_);
v_i_boxed_3274_ = lean_unbox_usize(v_i_3271_);
lean_dec(v_i_3271_);
v_stop_boxed_3275_ = lean_unbox_usize(v_stop_3272_);
lean_dec(v_stop_3272_);
v_res_3276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3273_, v_as_3270_, v_i_boxed_3274_, v_stop_boxed_3275_);
lean_dec_ref(v_as_3270_);
v_r_3277_ = lean_box(v_res_3276_);
return v_r_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3278_, lean_object* v_x_3279_){
_start:
{
uint8_t v___x_1834__boxed_3280_; uint8_t v_res_3281_; lean_object* v_r_3282_; 
v___x_1834__boxed_3280_ = lean_unbox(v___x_3278_);
v_res_3281_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3280_, v_x_3279_);
lean_dec_ref(v_x_3279_);
v_r_3282_ = lean_box(v_res_3281_);
return v_r_3282_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3283_, lean_object* v_t_3284_){
_start:
{
lean_object* v_root_3285_; lean_object* v_tail_3286_; uint8_t v___x_3287_; 
v_root_3285_ = lean_ctor_get(v_t_3284_, 0);
v_tail_3286_ = lean_ctor_get(v_t_3284_, 1);
v___x_3287_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3283_, v_root_3285_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3288_ = lean_unsigned_to_nat(0u);
v___x_3289_ = lean_array_get_size(v_tail_3286_);
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
v___x_3293_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3283_, v_tail_3286_, v___x_3291_, v___x_3292_);
return v___x_3293_;
}
}
else
{
return v___x_3287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3294_, lean_object* v_t_3295_){
_start:
{
uint8_t v___x_1877__boxed_3296_; uint8_t v_res_3297_; lean_object* v_r_3298_; 
v___x_1877__boxed_3296_ = lean_unbox(v___x_3294_);
v_res_3297_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3296_, v_t_3295_);
lean_dec_ref(v_t_3295_);
v_r_3298_ = lean_box(v_res_3297_);
return v_r_3298_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3299_){
_start:
{
lean_object* v_reported_3300_; lean_object* v_unreported_3301_; uint8_t v___x_3302_; 
v_reported_3300_ = lean_ctor_get(v_log_3299_, 0);
v_unreported_3301_ = lean_ctor_get(v_log_3299_, 1);
v___x_3302_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3300_);
if (v___x_3302_ == 0)
{
uint8_t v___x_3303_; 
v___x_3303_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3302_, v_unreported_3301_);
return v___x_3303_;
}
else
{
return v___x_3302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3304_){
_start:
{
uint8_t v_res_3305_; lean_object* v_r_3306_; 
v_res_3305_ = l_Lean_MessageLog_hasErrors(v_log_3304_);
lean_dec_ref(v_log_3304_);
v_r_3306_ = lean_box(v_res_3305_);
return v_r_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3307_){
_start:
{
lean_object* v_reported_3308_; lean_object* v_unreported_3309_; lean_object* v_loggedKinds_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3321_; 
v_reported_3308_ = lean_ctor_get(v_log_3307_, 0);
v_unreported_3309_ = lean_ctor_get(v_log_3307_, 1);
v_loggedKinds_3310_ = lean_ctor_get(v_log_3307_, 2);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_log_3307_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3312_ = v_log_3307_;
v_isShared_3313_ = v_isSharedCheck_3321_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_loggedKinds_3310_);
lean_inc(v_unreported_3309_);
lean_inc(v_reported_3308_);
lean_dec(v_log_3307_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3321_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3314_ = l_Lean_PersistentArray_append___redArg(v_reported_3308_, v_unreported_3309_);
lean_dec_ref(v_unreported_3309_);
v___x_3315_ = lean_unsigned_to_nat(32u);
v___x_3316_ = lean_mk_empty_array_with_capacity(v___x_3315_);
lean_dec_ref(v___x_3316_);
v___x_3317_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 1, v___x_3317_);
lean_ctor_set(v___x_3312_, 0, v___x_3314_);
v___x_3319_ = v___x_3312_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_loggedKinds_3310_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3322_, size_t v_i_3323_, lean_object* v_bs_3324_){
_start:
{
uint8_t v___x_3325_; 
v___x_3325_ = lean_usize_dec_lt(v_i_3323_, v_sz_3322_);
if (v___x_3325_ == 0)
{
return v_bs_3324_;
}
else
{
lean_object* v_v_3326_; lean_object* v_fileName_3327_; lean_object* v_pos_3328_; lean_object* v_endPos_3329_; uint8_t v_keepFullRange_3330_; uint8_t v_severity_3331_; uint8_t v_isSilent_3332_; lean_object* v_caption_3333_; lean_object* v_data_3334_; lean_object* v___x_3335_; lean_object* v_bs_x27_3336_; lean_object* v___y_3338_; 
v_v_3326_ = lean_array_uget(v_bs_3324_, v_i_3323_);
v_fileName_3327_ = lean_ctor_get(v_v_3326_, 0);
v_pos_3328_ = lean_ctor_get(v_v_3326_, 1);
v_endPos_3329_ = lean_ctor_get(v_v_3326_, 2);
v_keepFullRange_3330_ = lean_ctor_get_uint8(v_v_3326_, sizeof(void*)*5);
v_severity_3331_ = lean_ctor_get_uint8(v_v_3326_, sizeof(void*)*5 + 1);
v_isSilent_3332_ = lean_ctor_get_uint8(v_v_3326_, sizeof(void*)*5 + 2);
v_caption_3333_ = lean_ctor_get(v_v_3326_, 3);
v_data_3334_ = lean_ctor_get(v_v_3326_, 4);
v___x_3335_ = lean_unsigned_to_nat(0u);
v_bs_x27_3336_ = lean_array_uset(v_bs_3324_, v_i_3323_, v___x_3335_);
if (v_severity_3331_ == 2)
{
lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3350_; 
lean_inc(v_data_3334_);
lean_inc_ref(v_caption_3333_);
lean_inc(v_endPos_3329_);
lean_inc_ref(v_pos_3328_);
lean_inc_ref(v_fileName_3327_);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_v_3326_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; lean_object* v_unused_3353_; lean_object* v_unused_3354_; lean_object* v_unused_3355_; 
v_unused_3351_ = lean_ctor_get(v_v_3326_, 4);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_v_3326_, 3);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_v_3326_, 2);
lean_dec(v_unused_3353_);
v_unused_3354_ = lean_ctor_get(v_v_3326_, 1);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_v_3326_, 0);
lean_dec(v_unused_3355_);
v___x_3344_ = v_v_3326_;
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v_v_3326_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3350_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
uint8_t v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = 1;
if (v_isShared_3345_ == 0)
{
v___x_3348_ = v___x_3344_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_fileName_3327_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_pos_3328_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_endPos_3329_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_caption_3333_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_data_3334_);
lean_ctor_set_uint8(v_reuseFailAlloc_3349_, sizeof(void*)*5, v_keepFullRange_3330_);
lean_ctor_set_uint8(v_reuseFailAlloc_3349_, sizeof(void*)*5 + 2, v_isSilent_3332_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*5 + 1, v___x_3346_);
v___y_3338_ = v___x_3348_;
goto v___jp_3337_;
}
}
}
else
{
v___y_3338_ = v_v_3326_;
goto v___jp_3337_;
}
v___jp_3337_:
{
size_t v___x_3339_; size_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_add(v_i_3323_, v___x_3339_);
v___x_3341_ = lean_array_uset(v_bs_x27_3336_, v_i_3323_, v___y_3338_);
v_i_3323_ = v___x_3340_;
v_bs_3324_ = v___x_3341_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3356_, lean_object* v_i_3357_, lean_object* v_bs_3358_){
_start:
{
size_t v_sz_boxed_3359_; size_t v_i_boxed_3360_; lean_object* v_res_3361_; 
v_sz_boxed_3359_ = lean_unbox_usize(v_sz_3356_);
lean_dec(v_sz_3356_);
v_i_boxed_3360_ = lean_unbox_usize(v_i_3357_);
lean_dec(v_i_3357_);
v_res_3361_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3359_, v_i_boxed_3360_, v_bs_3358_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3362_, size_t v_i_3363_, lean_object* v_bs_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3363_, v_sz_3362_);
if (v___x_3365_ == 0)
{
return v_bs_3364_;
}
else
{
lean_object* v_v_3366_; lean_object* v___x_3367_; lean_object* v_bs_x27_3368_; lean_object* v___x_3369_; size_t v___x_3370_; size_t v___x_3371_; lean_object* v___x_3372_; 
v_v_3366_ = lean_array_uget(v_bs_3364_, v_i_3363_);
v___x_3367_ = lean_unsigned_to_nat(0u);
v_bs_x27_3368_ = lean_array_uset(v_bs_3364_, v_i_3363_, v___x_3367_);
v___x_3369_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3366_);
v___x_3370_ = ((size_t)1ULL);
v___x_3371_ = lean_usize_add(v_i_3363_, v___x_3370_);
v___x_3372_ = lean_array_uset(v_bs_x27_3368_, v_i_3363_, v___x_3369_);
v_i_3363_ = v___x_3371_;
v_bs_3364_ = v___x_3372_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3374_){
_start:
{
if (lean_obj_tag(v_x_3374_) == 0)
{
lean_object* v_cs_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3385_; 
v_cs_3375_ = lean_ctor_get(v_x_3374_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_x_3374_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3377_ = v_x_3374_;
v_isShared_3378_ = v_isSharedCheck_3385_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_cs_3375_);
lean_dec(v_x_3374_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3385_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
size_t v_sz_3379_; size_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v_sz_3379_ = lean_array_size(v_cs_3375_);
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3379_, v___x_3380_, v_cs_3375_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 0, v___x_3381_);
v___x_3383_ = v___x_3377_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
lean_object* v_vs_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3396_; 
v_vs_3386_ = lean_ctor_get(v_x_3374_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_x_3374_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3388_ = v_x_3374_;
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_vs_3386_);
lean_dec(v_x_3374_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3396_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
size_t v_sz_3390_; size_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v_sz_3390_ = lean_array_size(v_vs_3386_);
v___x_3391_ = ((size_t)0ULL);
v___x_3392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3390_, v___x_3391_, v_vs_3386_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3392_);
v___x_3394_ = v___x_3388_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3397_, lean_object* v_i_3398_, lean_object* v_bs_3399_){
_start:
{
size_t v_sz_boxed_3400_; size_t v_i_boxed_3401_; lean_object* v_res_3402_; 
v_sz_boxed_3400_ = lean_unbox_usize(v_sz_3397_);
lean_dec(v_sz_3397_);
v_i_boxed_3401_ = lean_unbox_usize(v_i_3398_);
lean_dec(v_i_3398_);
v_res_3402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3400_, v_i_boxed_3401_, v_bs_3399_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3403_){
_start:
{
lean_object* v_root_3404_; lean_object* v_tail_3405_; lean_object* v_size_3406_; size_t v_shift_3407_; lean_object* v_tailOff_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3419_; 
v_root_3404_ = lean_ctor_get(v_t_3403_, 0);
v_tail_3405_ = lean_ctor_get(v_t_3403_, 1);
v_size_3406_ = lean_ctor_get(v_t_3403_, 2);
v_shift_3407_ = lean_ctor_get_usize(v_t_3403_, 4);
v_tailOff_3408_ = lean_ctor_get(v_t_3403_, 3);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_t_3403_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3410_ = v_t_3403_;
v_isShared_3411_ = v_isSharedCheck_3419_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_tailOff_3408_);
lean_inc(v_size_3406_);
lean_inc(v_tail_3405_);
lean_inc(v_root_3404_);
lean_dec(v_t_3403_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3419_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3412_; size_t v_sz_3413_; size_t v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3417_; 
v___x_3412_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3404_);
v_sz_3413_ = lean_array_size(v_tail_3405_);
v___x_3414_ = ((size_t)0ULL);
v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3413_, v___x_3414_, v_tail_3405_);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 1, v___x_3415_);
lean_ctor_set(v___x_3410_, 0, v___x_3412_);
v___x_3417_ = v___x_3410_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_size_3406_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_tailOff_3408_);
lean_ctor_set_usize(v_reuseFailAlloc_3418_, 4, v_shift_3407_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3420_){
_start:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v_unreported_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3433_; 
v___x_3421_ = lean_unsigned_to_nat(32u);
v___x_3422_ = lean_mk_empty_array_with_capacity(v___x_3421_);
lean_dec_ref(v___x_3422_);
v___x_3423_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3424_ = lean_ctor_get(v_log_3420_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_log_3420_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; lean_object* v_unused_3435_; 
v_unused_3434_ = lean_ctor_get(v_log_3420_, 2);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v_log_3420_, 0);
lean_dec(v_unused_3435_);
v___x_3426_ = v_log_3420_;
v_isShared_3427_ = v_isSharedCheck_3433_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_unreported_3424_);
lean_dec(v_log_3420_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3433_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3428_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3424_);
v___x_3429_ = l_Lean_NameSet_empty;
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 2, v___x_3429_);
lean_ctor_set(v___x_3426_, 1, v___x_3428_);
lean_ctor_set(v___x_3426_, 0, v___x_3423_);
v___x_3431_ = v___x_3426_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_bs_3438_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3439_ == 0)
{
return v_bs_3438_;
}
else
{
lean_object* v_v_3440_; lean_object* v_fileName_3441_; lean_object* v_pos_3442_; lean_object* v_endPos_3443_; uint8_t v_keepFullRange_3444_; uint8_t v_severity_3445_; uint8_t v_isSilent_3446_; lean_object* v_caption_3447_; lean_object* v_data_3448_; lean_object* v___x_3449_; lean_object* v_bs_x27_3450_; lean_object* v___y_3452_; 
v_v_3440_ = lean_array_uget(v_bs_3438_, v_i_3437_);
v_fileName_3441_ = lean_ctor_get(v_v_3440_, 0);
v_pos_3442_ = lean_ctor_get(v_v_3440_, 1);
v_endPos_3443_ = lean_ctor_get(v_v_3440_, 2);
v_keepFullRange_3444_ = lean_ctor_get_uint8(v_v_3440_, sizeof(void*)*5);
v_severity_3445_ = lean_ctor_get_uint8(v_v_3440_, sizeof(void*)*5 + 1);
v_isSilent_3446_ = lean_ctor_get_uint8(v_v_3440_, sizeof(void*)*5 + 2);
v_caption_3447_ = lean_ctor_get(v_v_3440_, 3);
v_data_3448_ = lean_ctor_get(v_v_3440_, 4);
v___x_3449_ = lean_unsigned_to_nat(0u);
v_bs_x27_3450_ = lean_array_uset(v_bs_3438_, v_i_3437_, v___x_3449_);
if (v_severity_3445_ == 2)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3464_; 
lean_inc(v_data_3448_);
lean_inc_ref(v_caption_3447_);
lean_inc(v_endPos_3443_);
lean_inc_ref(v_pos_3442_);
lean_inc_ref(v_fileName_3441_);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_v_3440_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; lean_object* v_unused_3467_; lean_object* v_unused_3468_; lean_object* v_unused_3469_; 
v_unused_3465_ = lean_ctor_get(v_v_3440_, 4);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_v_3440_, 3);
lean_dec(v_unused_3466_);
v_unused_3467_ = lean_ctor_get(v_v_3440_, 2);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_v_3440_, 1);
lean_dec(v_unused_3468_);
v_unused_3469_ = lean_ctor_get(v_v_3440_, 0);
lean_dec(v_unused_3469_);
v___x_3458_ = v_v_3440_;
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v_v_3440_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
uint8_t v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = 0;
if (v_isShared_3459_ == 0)
{
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_fileName_3441_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_pos_3442_);
lean_ctor_set(v_reuseFailAlloc_3463_, 2, v_endPos_3443_);
lean_ctor_set(v_reuseFailAlloc_3463_, 3, v_caption_3447_);
lean_ctor_set(v_reuseFailAlloc_3463_, 4, v_data_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3463_, sizeof(void*)*5, v_keepFullRange_3444_);
lean_ctor_set_uint8(v_reuseFailAlloc_3463_, sizeof(void*)*5 + 2, v_isSilent_3446_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*5 + 1, v___x_3460_);
v___y_3452_ = v___x_3462_;
goto v___jp_3451_;
}
}
}
else
{
v___y_3452_ = v_v_3440_;
goto v___jp_3451_;
}
v___jp_3451_:
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)1ULL);
v___x_3454_ = lean_usize_add(v_i_3437_, v___x_3453_);
v___x_3455_ = lean_array_uset(v_bs_x27_3450_, v_i_3437_, v___y_3452_);
v_i_3437_ = v___x_3454_;
v_bs_3438_ = v___x_3455_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3470_, lean_object* v_i_3471_, lean_object* v_bs_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3470_);
lean_dec(v_sz_3470_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3471_);
lean_dec(v_i_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3473_, v_i_boxed_3474_, v_bs_3472_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_bs_3478_){
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
lean_object* v_v_3480_; lean_object* v___x_3481_; lean_object* v_bs_x27_3482_; lean_object* v___x_3483_; size_t v___x_3484_; size_t v___x_3485_; lean_object* v___x_3486_; 
v_v_3480_ = lean_array_uget(v_bs_3478_, v_i_3477_);
v___x_3481_ = lean_unsigned_to_nat(0u);
v_bs_x27_3482_ = lean_array_uset(v_bs_3478_, v_i_3477_, v___x_3481_);
v___x_3483_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3480_);
v___x_3484_ = ((size_t)1ULL);
v___x_3485_ = lean_usize_add(v_i_3477_, v___x_3484_);
v___x_3486_ = lean_array_uset(v_bs_x27_3482_, v_i_3477_, v___x_3483_);
v_i_3477_ = v___x_3485_;
v_bs_3478_ = v___x_3486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
lean_object* v_cs_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3499_; 
v_cs_3489_ = lean_ctor_get(v_x_3488_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_x_3488_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3491_ = v_x_3488_;
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_cs_3489_);
lean_dec(v_x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3499_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
size_t v_sz_3493_; size_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v_sz_3493_ = lean_array_size(v_cs_3489_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3493_, v___x_3494_, v_cs_3489_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3495_);
v___x_3497_ = v___x_3491_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_vs_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3510_; 
v_vs_3500_ = lean_ctor_get(v_x_3488_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_x_3488_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3502_ = v_x_3488_;
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_vs_3500_);
lean_dec(v_x_3488_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3510_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
size_t v_sz_3504_; size_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v_sz_3504_ = lean_array_size(v_vs_3500_);
v___x_3505_ = ((size_t)0ULL);
v___x_3506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3504_, v___x_3505_, v_vs_3500_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 0, v___x_3506_);
v___x_3508_ = v___x_3502_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3511_, lean_object* v_i_3512_, lean_object* v_bs_3513_){
_start:
{
size_t v_sz_boxed_3514_; size_t v_i_boxed_3515_; lean_object* v_res_3516_; 
v_sz_boxed_3514_ = lean_unbox_usize(v_sz_3511_);
lean_dec(v_sz_3511_);
v_i_boxed_3515_ = lean_unbox_usize(v_i_3512_);
lean_dec(v_i_3512_);
v_res_3516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3514_, v_i_boxed_3515_, v_bs_3513_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3517_){
_start:
{
lean_object* v_root_3518_; lean_object* v_tail_3519_; lean_object* v_size_3520_; size_t v_shift_3521_; lean_object* v_tailOff_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3533_; 
v_root_3518_ = lean_ctor_get(v_t_3517_, 0);
v_tail_3519_ = lean_ctor_get(v_t_3517_, 1);
v_size_3520_ = lean_ctor_get(v_t_3517_, 2);
v_shift_3521_ = lean_ctor_get_usize(v_t_3517_, 4);
v_tailOff_3522_ = lean_ctor_get(v_t_3517_, 3);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_t_3517_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3524_ = v_t_3517_;
v_isShared_3525_ = v_isSharedCheck_3533_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_tailOff_3522_);
lean_inc(v_size_3520_);
lean_inc(v_tail_3519_);
lean_inc(v_root_3518_);
lean_dec(v_t_3517_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3533_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; size_t v_sz_3527_; size_t v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3526_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3518_);
v_sz_3527_ = lean_array_size(v_tail_3519_);
v___x_3528_ = ((size_t)0ULL);
v___x_3529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3527_, v___x_3528_, v_tail_3519_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3529_);
lean_ctor_set(v___x_3524_, 0, v___x_3526_);
v___x_3531_ = v___x_3524_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3529_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_size_3520_);
lean_ctor_set(v_reuseFailAlloc_3532_, 3, v_tailOff_3522_);
lean_ctor_set_usize(v_reuseFailAlloc_3532_, 4, v_shift_3521_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v_unreported_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3547_; 
v___x_3535_ = lean_unsigned_to_nat(32u);
v___x_3536_ = lean_mk_empty_array_with_capacity(v___x_3535_);
lean_dec_ref(v___x_3536_);
v___x_3537_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3538_ = lean_ctor_get(v_log_3534_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_log_3534_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3548_ = lean_ctor_get(v_log_3534_, 2);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_log_3534_, 0);
lean_dec(v_unused_3549_);
v___x_3540_ = v_log_3534_;
v_isShared_3541_ = v_isSharedCheck_3547_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_unreported_3538_);
lean_dec(v_log_3534_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3547_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3542_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3538_);
v___x_3543_ = l_Lean_NameSet_empty;
if (v_isShared_3541_ == 0)
{
lean_ctor_set(v___x_3540_, 2, v___x_3543_);
lean_ctor_set(v___x_3540_, 1, v___x_3542_);
lean_ctor_set(v___x_3540_, 0, v___x_3537_);
v___x_3545_ = v___x_3540_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v___x_3537_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3546_, 2, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3550_, size_t v_i_3551_, size_t v_stop_3552_, lean_object* v_b_3553_){
_start:
{
lean_object* v___y_3555_; uint8_t v___x_3559_; 
v___x_3559_ = lean_usize_dec_eq(v_i_3551_, v_stop_3552_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; uint8_t v_severity_3561_; 
v___x_3560_ = lean_array_uget_borrowed(v_as_3550_, v_i_3551_);
v_severity_3561_ = lean_ctor_get_uint8(v___x_3560_, sizeof(void*)*5 + 1);
if (v_severity_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_inc(v___x_3560_);
v___x_3562_ = l_Lean_PersistentArray_push___redArg(v_b_3553_, v___x_3560_);
v___y_3555_ = v___x_3562_;
goto v___jp_3554_;
}
else
{
v___y_3555_ = v_b_3553_;
goto v___jp_3554_;
}
}
else
{
return v_b_3553_;
}
v___jp_3554_:
{
size_t v___x_3556_; size_t v___x_3557_; 
v___x_3556_ = ((size_t)1ULL);
v___x_3557_ = lean_usize_add(v_i_3551_, v___x_3556_);
v_i_3551_ = v___x_3557_;
v_b_3553_ = v___y_3555_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3563_, lean_object* v_i_3564_, lean_object* v_stop_3565_, lean_object* v_b_3566_){
_start:
{
size_t v_i_boxed_3567_; size_t v_stop_boxed_3568_; lean_object* v_res_3569_; 
v_i_boxed_3567_ = lean_unbox_usize(v_i_3564_);
lean_dec(v_i_3564_);
v_stop_boxed_3568_ = lean_unbox_usize(v_stop_3565_);
lean_dec(v_stop_3565_);
v_res_3569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3563_, v_i_boxed_3567_, v_stop_boxed_3568_, v_b_3566_);
lean_dec_ref(v_as_3563_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3570_) == 0)
{
lean_object* v_cs_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v_cs_3572_ = lean_ctor_get(v_x_3570_, 0);
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_array_get_size(v_cs_3572_);
v___x_3575_ = lean_nat_dec_lt(v___x_3573_, v___x_3574_);
if (v___x_3575_ == 0)
{
return v_x_3571_;
}
else
{
size_t v___x_3576_; size_t v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = ((size_t)0ULL);
v___x_3577_ = lean_usize_of_nat(v___x_3574_);
v___x_3578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3572_, v___x_3576_, v___x_3577_, v_x_3571_);
return v___x_3578_;
}
}
else
{
lean_object* v_vs_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v_vs_3579_ = lean_ctor_get(v_x_3570_, 0);
v___x_3580_ = lean_unsigned_to_nat(0u);
v___x_3581_ = lean_array_get_size(v_vs_3579_);
v___x_3582_ = lean_nat_dec_lt(v___x_3580_, v___x_3581_);
if (v___x_3582_ == 0)
{
return v_x_3571_;
}
else
{
size_t v___x_3583_; size_t v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = ((size_t)0ULL);
v___x_3584_ = lean_usize_of_nat(v___x_3581_);
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3579_, v___x_3583_, v___x_3584_, v_x_3571_);
return v___x_3585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3586_, size_t v_i_3587_, size_t v_stop_3588_, lean_object* v_b_3589_){
_start:
{
uint8_t v___x_3590_; 
v___x_3590_ = lean_usize_dec_eq(v_i_3587_, v_stop_3588_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; 
v___x_3591_ = lean_array_uget_borrowed(v_as_3586_, v_i_3587_);
v___x_3592_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3591_, v_b_3589_);
v___x_3593_ = ((size_t)1ULL);
v___x_3594_ = lean_usize_add(v_i_3587_, v___x_3593_);
v_i_3587_ = v___x_3594_;
v_b_3589_ = v___x_3592_;
goto _start;
}
else
{
return v_b_3589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3596_, lean_object* v_i_3597_, lean_object* v_stop_3598_, lean_object* v_b_3599_){
_start:
{
size_t v_i_boxed_3600_; size_t v_stop_boxed_3601_; lean_object* v_res_3602_; 
v_i_boxed_3600_ = lean_unbox_usize(v_i_3597_);
lean_dec(v_i_3597_);
v_stop_boxed_3601_ = lean_unbox_usize(v_stop_3598_);
lean_dec(v_stop_3598_);
v_res_3602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3596_, v_i_boxed_3600_, v_stop_boxed_3601_, v_b_3599_);
lean_dec_ref(v_as_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3603_, v_x_3604_);
lean_dec_ref(v_x_3603_);
return v_res_3605_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3607_, size_t v_x_3608_, size_t v_x_3609_, lean_object* v_x_3610_){
_start:
{
if (lean_obj_tag(v_x_3607_) == 0)
{
lean_object* v_cs_3611_; lean_object* v___x_3612_; size_t v___x_3613_; lean_object* v_j_3614_; lean_object* v___x_3615_; size_t v___x_3616_; size_t v___x_3617_; size_t v___x_3618_; size_t v___x_3619_; size_t v___x_3620_; size_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v_cs_3611_ = lean_ctor_get(v_x_3607_, 0);
v___x_3612_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3613_ = lean_usize_shift_right(v_x_3608_, v_x_3609_);
v_j_3614_ = lean_usize_to_nat(v___x_3613_);
v___x_3615_ = lean_array_get_borrowed(v___x_3612_, v_cs_3611_, v_j_3614_);
v___x_3616_ = ((size_t)1ULL);
v___x_3617_ = lean_usize_shift_left(v___x_3616_, v_x_3609_);
v___x_3618_ = lean_usize_sub(v___x_3617_, v___x_3616_);
v___x_3619_ = lean_usize_land(v_x_3608_, v___x_3618_);
v___x_3620_ = ((size_t)5ULL);
v___x_3621_ = lean_usize_sub(v_x_3609_, v___x_3620_);
v___x_3622_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3615_, v___x_3619_, v___x_3621_, v_x_3610_);
v___x_3623_ = lean_unsigned_to_nat(1u);
v___x_3624_ = lean_nat_add(v_j_3614_, v___x_3623_);
lean_dec(v_j_3614_);
v___x_3625_ = lean_array_get_size(v_cs_3611_);
v___x_3626_ = lean_nat_dec_lt(v___x_3624_, v___x_3625_);
if (v___x_3626_ == 0)
{
lean_dec(v___x_3624_);
return v___x_3622_;
}
else
{
size_t v___x_3627_; size_t v___x_3628_; lean_object* v___x_3629_; 
v___x_3627_ = lean_usize_of_nat(v___x_3624_);
lean_dec(v___x_3624_);
v___x_3628_ = lean_usize_of_nat(v___x_3625_);
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3611_, v___x_3627_, v___x_3628_, v___x_3622_);
return v___x_3629_;
}
}
else
{
lean_object* v_vs_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; uint8_t v___x_3633_; 
v_vs_3630_ = lean_ctor_get(v_x_3607_, 0);
v___x_3631_ = lean_usize_to_nat(v_x_3608_);
v___x_3632_ = lean_array_get_size(v_vs_3630_);
v___x_3633_ = lean_nat_dec_lt(v___x_3631_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_dec(v___x_3631_);
return v_x_3610_;
}
else
{
size_t v___x_3634_; size_t v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_usize_of_nat(v___x_3631_);
lean_dec(v___x_3631_);
v___x_3635_ = lean_usize_of_nat(v___x_3632_);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3630_, v___x_3634_, v___x_3635_, v_x_3610_);
return v___x_3636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3637_, lean_object* v_x_3638_, lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
size_t v_x_1153__boxed_3641_; size_t v_x_1154__boxed_3642_; lean_object* v_res_3643_; 
v_x_1153__boxed_3641_ = lean_unbox_usize(v_x_3638_);
lean_dec(v_x_3638_);
v_x_1154__boxed_3642_ = lean_unbox_usize(v_x_3639_);
lean_dec(v_x_3639_);
v_res_3643_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3637_, v_x_1153__boxed_3641_, v_x_1154__boxed_3642_, v_x_3640_);
lean_dec_ref(v_x_3637_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3644_, lean_object* v_init_3645_, lean_object* v_start_3646_){
_start:
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = lean_nat_dec_eq(v_start_3646_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v_root_3649_; lean_object* v_tail_3650_; size_t v_shift_3651_; lean_object* v_tailOff_3652_; uint8_t v___x_3653_; 
v_root_3649_ = lean_ctor_get(v_t_3644_, 0);
v_tail_3650_ = lean_ctor_get(v_t_3644_, 1);
v_shift_3651_ = lean_ctor_get_usize(v_t_3644_, 4);
v_tailOff_3652_ = lean_ctor_get(v_t_3644_, 3);
v___x_3653_ = lean_nat_dec_le(v_tailOff_3652_, v_start_3646_);
if (v___x_3653_ == 0)
{
size_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3654_ = lean_usize_of_nat(v_start_3646_);
v___x_3655_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3649_, v___x_3654_, v_shift_3651_, v_init_3645_);
v___x_3656_ = lean_array_get_size(v_tail_3650_);
v___x_3657_ = lean_nat_dec_lt(v___x_3647_, v___x_3656_);
if (v___x_3657_ == 0)
{
return v___x_3655_;
}
else
{
size_t v___x_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = lean_usize_of_nat(v___x_3656_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3650_, v___x_3658_, v___x_3659_, v___x_3655_);
return v___x_3660_;
}
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3661_ = lean_nat_sub(v_start_3646_, v_tailOff_3652_);
v___x_3662_ = lean_array_get_size(v_tail_3650_);
v___x_3663_ = lean_nat_dec_lt(v___x_3661_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_dec(v___x_3661_);
return v_init_3645_;
}
else
{
size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_usize_of_nat(v___x_3661_);
lean_dec(v___x_3661_);
v___x_3665_ = lean_usize_of_nat(v___x_3662_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3650_, v___x_3664_, v___x_3665_, v_init_3645_);
return v___x_3666_;
}
}
}
else
{
lean_object* v_root_3667_; lean_object* v_tail_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_root_3667_ = lean_ctor_get(v_t_3644_, 0);
v_tail_3668_ = lean_ctor_get(v_t_3644_, 1);
v___x_3669_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3667_, v_init_3645_);
v___x_3670_ = lean_array_get_size(v_tail_3668_);
v___x_3671_ = lean_nat_dec_lt(v___x_3647_, v___x_3670_);
if (v___x_3671_ == 0)
{
return v___x_3669_;
}
else
{
size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = lean_usize_of_nat(v___x_3670_);
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3668_, v___x_3672_, v___x_3673_, v___x_3669_);
return v___x_3674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3675_, lean_object* v_init_3676_, lean_object* v_start_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3675_, v_init_3676_, v_start_3677_);
lean_dec(v_start_3677_);
lean_dec_ref(v_t_3675_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3679_){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_unreported_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3693_; 
v___x_3680_ = lean_unsigned_to_nat(32u);
v___x_3681_ = lean_mk_empty_array_with_capacity(v___x_3680_);
lean_dec_ref(v___x_3681_);
v___x_3682_ = lean_unsigned_to_nat(0u);
v___x_3683_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3684_ = lean_ctor_get(v_log_3679_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_log_3679_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; lean_object* v_unused_3695_; 
v_unused_3694_ = lean_ctor_get(v_log_3679_, 2);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_log_3679_, 0);
lean_dec(v_unused_3695_);
v___x_3686_ = v_log_3679_;
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_unreported_3684_);
lean_dec(v_log_3679_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3688_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3684_, v___x_3683_, v___x_3682_);
lean_dec_ref(v_unreported_3684_);
v___x_3689_ = l_Lean_NameSet_empty;
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 2, v___x_3689_);
lean_ctor_set(v___x_3686_, 1, v___x_3688_);
lean_ctor_set(v___x_3686_, 0, v___x_3683_);
v___x_3691_ = v___x_3686_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3683_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3696_, size_t v_i_3697_, size_t v_stop_3698_, lean_object* v_b_3699_){
_start:
{
lean_object* v___y_3701_; uint8_t v___x_3705_; 
v___x_3705_ = lean_usize_dec_eq(v_i_3697_, v_stop_3698_);
if (v___x_3705_ == 0)
{
lean_object* v___x_3706_; uint8_t v_severity_3707_; 
v___x_3706_ = lean_array_uget_borrowed(v_as_3696_, v_i_3697_);
v_severity_3707_ = lean_ctor_get_uint8(v___x_3706_, sizeof(void*)*5 + 1);
if (v_severity_3707_ == 1)
{
lean_object* v___x_3708_; 
lean_inc(v___x_3706_);
v___x_3708_ = l_Lean_PersistentArray_push___redArg(v_b_3699_, v___x_3706_);
v___y_3701_ = v___x_3708_;
goto v___jp_3700_;
}
else
{
v___y_3701_ = v_b_3699_;
goto v___jp_3700_;
}
}
else
{
return v_b_3699_;
}
v___jp_3700_:
{
size_t v___x_3702_; size_t v___x_3703_; 
v___x_3702_ = ((size_t)1ULL);
v___x_3703_ = lean_usize_add(v_i_3697_, v___x_3702_);
v_i_3697_ = v___x_3703_;
v_b_3699_ = v___y_3701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3709_, lean_object* v_i_3710_, lean_object* v_stop_3711_, lean_object* v_b_3712_){
_start:
{
size_t v_i_boxed_3713_; size_t v_stop_boxed_3714_; lean_object* v_res_3715_; 
v_i_boxed_3713_ = lean_unbox_usize(v_i_3710_);
lean_dec(v_i_3710_);
v_stop_boxed_3714_ = lean_unbox_usize(v_stop_3711_);
lean_dec(v_stop_3711_);
v_res_3715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3709_, v_i_boxed_3713_, v_stop_boxed_3714_, v_b_3712_);
lean_dec_ref(v_as_3709_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
if (lean_obj_tag(v_x_3716_) == 0)
{
lean_object* v_cs_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v_cs_3718_ = lean_ctor_get(v_x_3716_, 0);
v___x_3719_ = lean_unsigned_to_nat(0u);
v___x_3720_ = lean_array_get_size(v_cs_3718_);
v___x_3721_ = lean_nat_dec_lt(v___x_3719_, v___x_3720_);
if (v___x_3721_ == 0)
{
return v_x_3717_;
}
else
{
size_t v___x_3722_; size_t v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = ((size_t)0ULL);
v___x_3723_ = lean_usize_of_nat(v___x_3720_);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3718_, v___x_3722_, v___x_3723_, v_x_3717_);
return v___x_3724_;
}
}
else
{
lean_object* v_vs_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v_vs_3725_ = lean_ctor_get(v_x_3716_, 0);
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_array_get_size(v_vs_3725_);
v___x_3728_ = lean_nat_dec_lt(v___x_3726_, v___x_3727_);
if (v___x_3728_ == 0)
{
return v_x_3717_;
}
else
{
size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = lean_usize_of_nat(v___x_3727_);
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3725_, v___x_3729_, v___x_3730_, v_x_3717_);
return v___x_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3732_, size_t v_i_3733_, size_t v_stop_3734_, lean_object* v_b_3735_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_usize_dec_eq(v_i_3733_, v_stop_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; size_t v___x_3739_; size_t v___x_3740_; 
v___x_3737_ = lean_array_uget_borrowed(v_as_3732_, v_i_3733_);
v___x_3738_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3737_, v_b_3735_);
v___x_3739_ = ((size_t)1ULL);
v___x_3740_ = lean_usize_add(v_i_3733_, v___x_3739_);
v_i_3733_ = v___x_3740_;
v_b_3735_ = v___x_3738_;
goto _start;
}
else
{
return v_b_3735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3742_, lean_object* v_i_3743_, lean_object* v_stop_3744_, lean_object* v_b_3745_){
_start:
{
size_t v_i_boxed_3746_; size_t v_stop_boxed_3747_; lean_object* v_res_3748_; 
v_i_boxed_3746_ = lean_unbox_usize(v_i_3743_);
lean_dec(v_i_3743_);
v_stop_boxed_3747_ = lean_unbox_usize(v_stop_3744_);
lean_dec(v_stop_3744_);
v_res_3748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3742_, v_i_boxed_3746_, v_stop_boxed_3747_, v_b_3745_);
lean_dec_ref(v_as_3742_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3749_, lean_object* v_x_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3749_, v_x_3750_);
lean_dec_ref(v_x_3749_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3752_, size_t v_x_3753_, size_t v_x_3754_, lean_object* v_x_3755_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 0)
{
lean_object* v_cs_3756_; lean_object* v___x_3757_; size_t v___x_3758_; lean_object* v_j_3759_; lean_object* v___x_3760_; size_t v___x_3761_; size_t v___x_3762_; size_t v___x_3763_; size_t v___x_3764_; size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_cs_3756_ = lean_ctor_get(v_x_3752_, 0);
v___x_3757_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3758_ = lean_usize_shift_right(v_x_3753_, v_x_3754_);
v_j_3759_ = lean_usize_to_nat(v___x_3758_);
v___x_3760_ = lean_array_get_borrowed(v___x_3757_, v_cs_3756_, v_j_3759_);
v___x_3761_ = ((size_t)1ULL);
v___x_3762_ = lean_usize_shift_left(v___x_3761_, v_x_3754_);
v___x_3763_ = lean_usize_sub(v___x_3762_, v___x_3761_);
v___x_3764_ = lean_usize_land(v_x_3753_, v___x_3763_);
v___x_3765_ = ((size_t)5ULL);
v___x_3766_ = lean_usize_sub(v_x_3754_, v___x_3765_);
v___x_3767_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3760_, v___x_3764_, v___x_3766_, v_x_3755_);
v___x_3768_ = lean_unsigned_to_nat(1u);
v___x_3769_ = lean_nat_add(v_j_3759_, v___x_3768_);
lean_dec(v_j_3759_);
v___x_3770_ = lean_array_get_size(v_cs_3756_);
v___x_3771_ = lean_nat_dec_lt(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec(v___x_3769_);
return v___x_3767_;
}
else
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_usize_of_nat(v___x_3769_);
lean_dec(v___x_3769_);
v___x_3773_ = lean_usize_of_nat(v___x_3770_);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3756_, v___x_3772_, v___x_3773_, v___x_3767_);
return v___x_3774_;
}
}
else
{
lean_object* v_vs_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_vs_3775_ = lean_ctor_get(v_x_3752_, 0);
v___x_3776_ = lean_usize_to_nat(v_x_3753_);
v___x_3777_ = lean_array_get_size(v_vs_3775_);
v___x_3778_ = lean_nat_dec_lt(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_dec(v___x_3776_);
return v_x_3755_;
}
else
{
size_t v___x_3779_; size_t v___x_3780_; lean_object* v___x_3781_; 
v___x_3779_ = lean_usize_of_nat(v___x_3776_);
lean_dec(v___x_3776_);
v___x_3780_ = lean_usize_of_nat(v___x_3777_);
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3775_, v___x_3779_, v___x_3780_, v_x_3755_);
return v___x_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_){
_start:
{
size_t v_x_1152__boxed_3786_; size_t v_x_1153__boxed_3787_; lean_object* v_res_3788_; 
v_x_1152__boxed_3786_ = lean_unbox_usize(v_x_3783_);
lean_dec(v_x_3783_);
v_x_1153__boxed_3787_ = lean_unbox_usize(v_x_3784_);
lean_dec(v_x_3784_);
v_res_3788_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3782_, v_x_1152__boxed_3786_, v_x_1153__boxed_3787_, v_x_3785_);
lean_dec_ref(v_x_3782_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3789_, lean_object* v_init_3790_, lean_object* v_start_3791_){
_start:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3792_ = lean_unsigned_to_nat(0u);
v___x_3793_ = lean_nat_dec_eq(v_start_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v_root_3794_; lean_object* v_tail_3795_; size_t v_shift_3796_; lean_object* v_tailOff_3797_; uint8_t v___x_3798_; 
v_root_3794_ = lean_ctor_get(v_t_3789_, 0);
v_tail_3795_ = lean_ctor_get(v_t_3789_, 1);
v_shift_3796_ = lean_ctor_get_usize(v_t_3789_, 4);
v_tailOff_3797_ = lean_ctor_get(v_t_3789_, 3);
v___x_3798_ = lean_nat_dec_le(v_tailOff_3797_, v_start_3791_);
if (v___x_3798_ == 0)
{
size_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3799_ = lean_usize_of_nat(v_start_3791_);
v___x_3800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3794_, v___x_3799_, v_shift_3796_, v_init_3790_);
v___x_3801_ = lean_array_get_size(v_tail_3795_);
v___x_3802_ = lean_nat_dec_lt(v___x_3792_, v___x_3801_);
if (v___x_3802_ == 0)
{
return v___x_3800_;
}
else
{
size_t v___x_3803_; size_t v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = ((size_t)0ULL);
v___x_3804_ = lean_usize_of_nat(v___x_3801_);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3795_, v___x_3803_, v___x_3804_, v___x_3800_);
return v___x_3805_;
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
v___x_3806_ = lean_nat_sub(v_start_3791_, v_tailOff_3797_);
v___x_3807_ = lean_array_get_size(v_tail_3795_);
v___x_3808_ = lean_nat_dec_lt(v___x_3806_, v___x_3807_);
if (v___x_3808_ == 0)
{
lean_dec(v___x_3806_);
return v_init_3790_;
}
else
{
size_t v___x_3809_; size_t v___x_3810_; lean_object* v___x_3811_; 
v___x_3809_ = lean_usize_of_nat(v___x_3806_);
lean_dec(v___x_3806_);
v___x_3810_ = lean_usize_of_nat(v___x_3807_);
v___x_3811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3795_, v___x_3809_, v___x_3810_, v_init_3790_);
return v___x_3811_;
}
}
}
else
{
lean_object* v_root_3812_; lean_object* v_tail_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_root_3812_ = lean_ctor_get(v_t_3789_, 0);
v_tail_3813_ = lean_ctor_get(v_t_3789_, 1);
v___x_3814_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3812_, v_init_3790_);
v___x_3815_ = lean_array_get_size(v_tail_3813_);
v___x_3816_ = lean_nat_dec_lt(v___x_3792_, v___x_3815_);
if (v___x_3816_ == 0)
{
return v___x_3814_;
}
else
{
size_t v___x_3817_; size_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = ((size_t)0ULL);
v___x_3818_ = lean_usize_of_nat(v___x_3815_);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3813_, v___x_3817_, v___x_3818_, v___x_3814_);
return v___x_3819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3820_, lean_object* v_init_3821_, lean_object* v_start_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3820_, v_init_3821_, v_start_3822_);
lean_dec(v_start_3822_);
lean_dec_ref(v_t_3820_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3824_){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v_unreported_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3838_; 
v___x_3825_ = lean_unsigned_to_nat(32u);
v___x_3826_ = lean_mk_empty_array_with_capacity(v___x_3825_);
lean_dec_ref(v___x_3826_);
v___x_3827_ = lean_unsigned_to_nat(0u);
v___x_3828_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3829_ = lean_ctor_get(v_log_3824_, 1);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_log_3824_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; lean_object* v_unused_3840_; 
v_unused_3839_ = lean_ctor_get(v_log_3824_, 2);
lean_dec(v_unused_3839_);
v_unused_3840_ = lean_ctor_get(v_log_3824_, 0);
lean_dec(v_unused_3840_);
v___x_3831_ = v_log_3824_;
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_unreported_3829_);
lean_dec(v_log_3824_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3833_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3829_, v___x_3828_, v___x_3827_);
lean_dec_ref(v_unreported_3829_);
v___x_3834_ = l_Lean_NameSet_empty;
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 2, v___x_3834_);
lean_ctor_set(v___x_3831_, 1, v___x_3833_);
lean_ctor_set(v___x_3831_, 0, v___x_3828_);
v___x_3836_ = v___x_3831_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3828_);
lean_ctor_set(v_reuseFailAlloc_3837_, 1, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3837_, 2, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3841_, lean_object* v_log_3842_, lean_object* v_f_3843_){
_start:
{
lean_object* v_unreported_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_unreported_3844_ = lean_ctor_get(v_log_3842_, 1);
lean_inc_ref(v_unreported_3844_);
lean_dec_ref(v_log_3842_);
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = l_Lean_PersistentArray_forM___redArg(v_inst_3841_, v_unreported_3844_, v_f_3843_, v___x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3847_, lean_object* v_inst_3848_, lean_object* v_log_3849_, lean_object* v_f_3850_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_MessageLog_forM___redArg(v_inst_3848_, v_log_3849_, v_f_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3852_){
_start:
{
lean_object* v_unreported_3853_; lean_object* v___x_3854_; 
v_unreported_3853_ = lean_ctor_get(v_log_3852_, 1);
v___x_3854_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_MessageLog_toList(v_log_3855_);
lean_dec_ref(v_log_3855_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3857_){
_start:
{
lean_object* v_unreported_3858_; lean_object* v___x_3859_; 
v_unreported_3858_ = lean_ctor_get(v_log_3857_, 1);
v___x_3859_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3858_);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_MessageLog_toArray(v_log_3860_);
lean_dec_ref(v_log_3860_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_3862_){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_unsigned_to_nat(2u);
v___x_3864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3863_);
lean_ctor_set(v___x_3864_, 1, v_msg_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_3865_){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_3867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v_msg_3865_);
v___x_3868_ = l_Lean_MessageData_nestD(v___x_3867_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_3869_){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = l_Lean_MessageData_ofExpr(v_e_3869_);
v___x_3871_ = l_Lean_indentD(v___x_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_3872_, lean_object* v_msg_3873_){
_start:
{
lean_object* v_env_3875_; lean_object* v_mctx_3876_; lean_object* v_lctx_3877_; lean_object* v_opts_3878_; lean_object* v_currNamespace_3879_; lean_object* v_openDecls_3880_; lean_object* v___x_3881_; lean_object* v_msg_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_env_3875_ = lean_ctor_get(v_ctx_3872_, 0);
v_mctx_3876_ = lean_ctor_get(v_ctx_3872_, 1);
v_lctx_3877_ = lean_ctor_get(v_ctx_3872_, 2);
v_opts_3878_ = lean_ctor_get(v_ctx_3872_, 3);
v_currNamespace_3879_ = lean_ctor_get(v_ctx_3872_, 4);
v_openDecls_3880_ = lean_ctor_get(v_ctx_3872_, 5);
lean_inc(v_openDecls_3880_);
lean_inc(v_currNamespace_3879_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_currNamespace_3879_);
lean_ctor_set(v___x_3881_, 1, v_openDecls_3880_);
v_msg_3882_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_3882_, 0, v___x_3881_);
lean_ctor_set(v_msg_3882_, 1, v_msg_3873_);
lean_inc_ref(v_opts_3878_);
lean_inc_ref(v_lctx_3877_);
lean_inc_ref(v_mctx_3876_);
lean_inc_ref(v_env_3875_);
v___x_3883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3883_, 0, v_env_3875_);
lean_ctor_set(v___x_3883_, 1, v_mctx_3876_);
lean_ctor_set(v___x_3883_, 2, v_lctx_3877_);
lean_ctor_set(v___x_3883_, 3, v_opts_3878_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
v___x_3885_ = l_Lean_MessageData_format(v_msg_3882_, v___x_3884_);
v___x_3886_ = l_Std_Format_defWidth;
v___x_3887_ = lean_unsigned_to_nat(0u);
v___x_3888_ = l_Std_Format_pretty(v___x_3885_, v___x_3886_, v___x_3887_, v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_3889_, lean_object* v_msg_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3889_, v_msg_3890_);
lean_dec_ref(v_ctx_3889_);
return v_res_3892_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_3893_, lean_object* v_a_3894_, uint8_t v_b_3895_){
_start:
{
lean_object* v_str_3896_; lean_object* v_startInclusive_3897_; lean_object* v_endExclusive_3898_; lean_object* v___x_3899_; uint8_t v_decide_3900_; 
v_str_3896_ = lean_ctor_get(v_s_3893_, 0);
v_startInclusive_3897_ = lean_ctor_get(v_s_3893_, 1);
v_endExclusive_3898_ = lean_ctor_get(v_s_3893_, 2);
v___x_3899_ = lean_nat_sub(v_endExclusive_3898_, v_startInclusive_3897_);
v_decide_3900_ = lean_nat_dec_eq(v_a_3894_, v___x_3899_);
lean_dec(v___x_3899_);
if (v_decide_3900_ == 0)
{
lean_object* v___x_3901_; uint32_t v___x_3902_; uint32_t v___x_3903_; uint8_t v___x_3904_; 
v___x_3901_ = lean_nat_add(v_startInclusive_3897_, v_a_3894_);
lean_dec(v_a_3894_);
v___x_3902_ = lean_string_utf8_get_fast(v_str_3896_, v___x_3901_);
v___x_3903_ = 10;
v___x_3904_ = lean_uint32_dec_eq(v___x_3902_, v___x_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_string_utf8_next_fast(v_str_3896_, v___x_3901_);
lean_dec(v___x_3901_);
v___x_3906_ = lean_nat_sub(v___x_3905_, v_startInclusive_3897_);
v_a_3894_ = v___x_3906_;
v_b_3895_ = v___x_3904_;
goto _start;
}
else
{
lean_dec(v___x_3901_);
return v___x_3904_;
}
}
else
{
lean_dec(v_a_3894_);
return v_b_3895_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_3908_, lean_object* v_a_3909_, lean_object* v_b_3910_){
_start:
{
uint8_t v_b_boxed_3911_; uint8_t v_res_3912_; lean_object* v_r_3913_; 
v_b_boxed_3911_ = lean_unbox(v_b_3910_);
v_res_3912_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3908_, v_a_3909_, v_b_boxed_3911_);
lean_dec_ref(v_s_3908_);
v_r_3913_ = lean_box(v_res_3912_);
return v_r_3913_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_3914_){
_start:
{
lean_object* v_searcher_3915_; uint8_t v___x_3916_; uint8_t v___x_3917_; 
v_searcher_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = 0;
v___x_3917_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_3914_, v_searcher_3915_, v___x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_3918_){
_start:
{
uint8_t v_res_3919_; lean_object* v_r_3920_; 
v_res_3919_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_3918_);
lean_dec_ref(v_s_3918_);
v_r_3920_ = lean_box(v_res_3919_);
return v_r_3920_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_3921_, lean_object* v_val_3922_, lean_object* v_a_3923_, lean_object* v_b_3924_){
_start:
{
uint8_t v_decide_3925_; 
v_decide_3925_ = lean_nat_dec_eq(v_a_3923_, v___x_3921_);
if (v_decide_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_string_utf8_next_fast(v_val_3922_, v_a_3923_);
lean_dec(v_a_3923_);
v___x_3927_ = lean_unsigned_to_nat(1u);
v___x_3928_ = lean_nat_add(v_b_3924_, v___x_3927_);
lean_dec(v_b_3924_);
v_a_3923_ = v___x_3926_;
v_b_3924_ = v___x_3928_;
goto _start;
}
else
{
lean_dec(v_a_3923_);
return v_b_3924_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_3930_, lean_object* v_val_3931_, lean_object* v_a_3932_, lean_object* v_b_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3930_, v_val_3931_, v_a_3932_, v_b_3933_);
lean_dec_ref(v_val_3931_);
lean_dec(v___x_3930_);
return v_res_3934_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_3936_ = l_Lean_MessageData_ofFormat(v___x_3935_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3940_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_3941_ = l_Lean_MessageData_ofFormat(v___x_3940_);
return v___x_3941_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3945_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_3946_ = l_Lean_MessageData_ofFormat(v___x_3945_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_3947_, lean_object* v_maxInlineLength_3948_, lean_object* v_ctx_3949_){
_start:
{
lean_object* v_msg_3951_; lean_object* v___x_3952_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; uint8_t v___x_3961_; 
v_msg_3951_ = l_Lean_MessageData_ofExpr(v_e_3947_);
lean_inc_ref(v_msg_3951_);
v___x_3952_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_3949_, v_msg_3951_);
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = lean_string_utf8_byte_size(v___x_3952_);
lean_inc_ref(v___x_3952_);
v___x_3959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3952_);
lean_ctor_set(v___x_3959_, 1, v___x_3957_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
v___x_3960_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3958_, v___x_3952_, v___x_3957_, v___x_3957_);
lean_dec_ref(v___x_3952_);
v___x_3961_ = lean_nat_dec_lt(v_maxInlineLength_3948_, v___x_3960_);
lean_dec(v___x_3960_);
if (v___x_3961_ == 0)
{
uint8_t v___x_3962_; 
v___x_3962_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_3959_);
lean_dec_ref_known(v___x_3959_, 3);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3963_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v_msg_3951_);
v___x_3965_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
return v___x_3966_;
}
else
{
goto v___jp_3953_;
}
}
else
{
lean_dec_ref_known(v___x_3959_, 3);
goto v___jp_3953_;
}
v___jp_3953_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = l_Lean_indentD(v_msg_3951_);
v___x_3955_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_3967_, lean_object* v_maxInlineLength_3968_, lean_object* v_ctx_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_Lean_inlineExpr___lam__0(v_e_3967_, v_maxInlineLength_3968_, v_ctx_3969_);
lean_dec_ref(v_ctx_3969_);
lean_dec(v_maxInlineLength_3968_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_3972_, lean_object* v_x_3973_){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3975_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_3976_ = l_Lean_MessageData_ofExpr(v_e_3972_);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_inlineExpr___lam__2(v_e_3980_, v_x_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_3984_, lean_object* v_maxInlineLength_3985_){
_start:
{
lean_object* v___f_3986_; lean_object* v___f_3987_; lean_object* v___f_3988_; lean_object* v___x_3989_; 
lean_inc_ref_n(v_e_3984_, 2);
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3986_, 0, v_e_3984_);
lean_closure_set(v___f_3986_, 1, v_maxInlineLength_3985_);
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3987_, 0, v_e_3984_);
v___f_3988_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_3988_, 0, v_e_3984_);
v___x_3989_ = l_Lean_MessageData_lazy(v___f_3986_, v___f_3987_, v___f_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_3990_, lean_object* v___x_3991_, lean_object* v_val_3992_, lean_object* v_inst_3993_, lean_object* v_R_3994_, lean_object* v_a_3995_, lean_object* v_b_3996_, lean_object* v_c_3997_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_3990_, v_val_3992_, v_a_3995_, v_b_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_3999_, lean_object* v___x_4000_, lean_object* v_val_4001_, lean_object* v_inst_4002_, lean_object* v_R_4003_, lean_object* v_a_4004_, lean_object* v_b_4005_, lean_object* v_c_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_3999_, v___x_4000_, v_val_4001_, v_inst_4002_, v_R_4003_, v_a_4004_, v_b_4005_, v_c_4006_);
lean_dec_ref(v_val_4001_);
lean_dec_ref(v___x_4000_);
lean_dec(v___x_3999_);
return v_res_4007_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4008_, lean_object* v_inst_4009_, lean_object* v_R_4010_, lean_object* v_a_4011_, uint8_t v_b_4012_, lean_object* v_c_4013_){
_start:
{
uint8_t v___x_4014_; 
v___x_4014_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4008_, v_a_4011_, v_b_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4015_, lean_object* v_inst_4016_, lean_object* v_R_4017_, lean_object* v_a_4018_, lean_object* v_b_4019_, lean_object* v_c_4020_){
_start:
{
uint8_t v_b_boxed_4021_; uint8_t v_res_4022_; lean_object* v_r_4023_; 
v_b_boxed_4021_ = lean_unbox(v_b_4019_);
v_res_4022_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4015_, v_inst_4016_, v_R_4017_, v_a_4018_, v_b_boxed_4021_, v_c_4020_);
lean_dec_ref(v_s_4015_);
v_r_4023_ = lean_box(v_res_4022_);
return v_r_4023_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4028_ = l_Lean_MessageData_ofFormat(v___x_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4029_, lean_object* v_maxInlineLength_4030_, lean_object* v_ctx_4031_){
_start:
{
lean_object* v_msg_4033_; lean_object* v___x_4034_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v_msg_4033_ = l_Lean_MessageData_ofExpr(v_e_4029_);
lean_inc_ref(v_msg_4033_);
v___x_4034_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4031_, v_msg_4033_);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = lean_string_utf8_byte_size(v___x_4034_);
lean_inc_ref(v___x_4034_);
v___x_4039_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4034_);
lean_ctor_set(v___x_4039_, 1, v___x_4037_);
lean_ctor_set(v___x_4039_, 2, v___x_4038_);
v___x_4040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4038_, v___x_4034_, v___x_4037_, v___x_4037_);
lean_dec_ref(v___x_4034_);
v___x_4041_ = lean_nat_dec_lt(v_maxInlineLength_4030_, v___x_4040_);
lean_dec(v___x_4040_);
if (v___x_4041_ == 0)
{
uint8_t v___x_4042_; 
v___x_4042_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4039_);
lean_dec_ref_known(v___x_4039_, 3);
if (v___x_4042_ == 0)
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4043_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v_msg_4033_);
v___x_4045_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
return v___x_4046_;
}
else
{
goto v___jp_4035_;
}
}
else
{
lean_dec_ref_known(v___x_4039_, 3);
goto v___jp_4035_;
}
v___jp_4035_:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_indentD(v_msg_4033_);
return v___x_4036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4047_, lean_object* v_maxInlineLength_4048_, lean_object* v_ctx_4049_, lean_object* v___y_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_inlineExprTrailing___lam__0(v_e_4047_, v_maxInlineLength_4048_, v_ctx_4049_);
lean_dec_ref(v_ctx_4049_);
lean_dec(v_maxInlineLength_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4052_, lean_object* v_x_4053_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4055_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4056_ = l_Lean_MessageData_ofExpr(v_e_4052_);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4060_, lean_object* v_x_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_inlineExprTrailing___lam__2(v_e_4060_, v_x_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4064_, lean_object* v_maxInlineLength_4065_){
_start:
{
lean_object* v___f_4066_; lean_object* v___f_4067_; lean_object* v___f_4068_; lean_object* v___x_4069_; 
lean_inc_ref_n(v_e_4064_, 2);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4066_, 0, v_e_4064_);
lean_closure_set(v___f_4066_, 1, v_maxInlineLength_4065_);
v___f_4067_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4067_, 0, v_e_4064_);
v___f_4068_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4068_, 0, v_e_4064_);
v___x_4069_ = l_Lean_MessageData_lazy(v___f_4066_, v___f_4067_, v___f_4068_);
return v___x_4069_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4074_ = l_Lean_MessageData_ofFormat(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4079_ = l_Lean_MessageData_ofFormat(v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4080_){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4081_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_msg_4080_);
v___x_4083_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4082_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4085_, lean_object* v_inst_4086_, lean_object* v_msg_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_apply_1(v_inst_4085_, v_msg_4087_);
v___x_4089_ = lean_apply_2(v_inst_4086_, lean_box(0), v___x_4088_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4090_, lean_object* v_inst_4091_){
_start:
{
lean_object* v___f_4092_; 
v___f_4092_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4092_, 0, v_inst_4091_);
lean_closure_set(v___f_4092_, 1, v_inst_4090_);
return v___f_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4093_, lean_object* v_n_4094_, lean_object* v_inst_4095_, lean_object* v_inst_4096_){
_start:
{
lean_object* v___f_4097_; 
v___f_4097_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4097_, 0, v_inst_4096_);
lean_closure_set(v___f_4097_, 1, v_inst_4095_);
return v___f_4097_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_unsigned_to_nat(32u);
v___x_4099_ = lean_mk_empty_array_with_capacity(v___x_4098_);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4101_ = ((size_t)5ULL);
v___x_4102_ = lean_unsigned_to_nat(0u);
v___x_4103_ = lean_unsigned_to_nat(32u);
v___x_4104_ = lean_mk_empty_array_with_capacity(v___x_4103_);
v___x_4105_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4106_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v___x_4104_);
lean_ctor_set(v___x_4106_, 2, v___x_4102_);
lean_ctor_set(v___x_4106_, 3, v___x_4102_);
lean_ctor_set_usize(v___x_4106_, 4, v___x_4101_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4107_ = lean_box(1);
v___x_4108_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4109_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v___x_4108_);
lean_ctor_set(v___x_4110_, 2, v___x_4107_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4111_, lean_object* v_msgData_4112_, lean_object* v_toPure_4113_, lean_object* v_opts_4114_){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4115_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4116_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4117_, 0, v_env_4111_);
lean_ctor_set(v___x_4117_, 1, v___x_4115_);
lean_ctor_set(v___x_4117_, 2, v___x_4116_);
lean_ctor_set(v___x_4117_, 3, v_opts_4114_);
v___x_4118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v_msgData_4112_);
v___x_4119_ = lean_apply_2(v_toPure_4113_, lean_box(0), v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_inst_4120_, lean_object* v_msgData_4121_, lean_object* v_toPure_4122_, lean_object* v_toBind_4123_, lean_object* v_____do__lift_4124_){
_start:
{
lean_object* v_getOptionsUnrestricted_4125_; uint8_t v___x_4126_; lean_object* v_env_4127_; lean_object* v___f_4128_; lean_object* v___x_4129_; 
v_getOptionsUnrestricted_4125_ = lean_ctor_get(v_inst_4120_, 1);
lean_inc(v_getOptionsUnrestricted_4125_);
lean_dec_ref(v_inst_4120_);
v___x_4126_ = 0;
v_env_4127_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4124_, v___x_4126_);
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4128_, 0, v_env_4127_);
lean_closure_set(v___f_4128_, 1, v_msgData_4121_);
lean_closure_set(v___f_4128_, 2, v_toPure_4122_);
v___x_4129_ = lean_apply_4(v_toBind_4123_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4125_, v___f_4128_);
return v___x_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_inst_4132_, lean_object* v_msgData_4133_){
_start:
{
lean_object* v_toApplicative_4134_; lean_object* v_toBind_4135_; lean_object* v_getEnv_4136_; lean_object* v_toPure_4137_; lean_object* v___f_4138_; lean_object* v___x_4139_; 
v_toApplicative_4134_ = lean_ctor_get(v_inst_4130_, 0);
lean_inc_ref(v_toApplicative_4134_);
v_toBind_4135_ = lean_ctor_get(v_inst_4130_, 1);
lean_inc_n(v_toBind_4135_, 2);
lean_dec_ref(v_inst_4130_);
v_getEnv_4136_ = lean_ctor_get(v_inst_4131_, 0);
lean_inc(v_getEnv_4136_);
lean_dec_ref(v_inst_4131_);
v_toPure_4137_ = lean_ctor_get(v_toApplicative_4134_, 1);
lean_inc(v_toPure_4137_);
lean_dec_ref(v_toApplicative_4134_);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4138_, 0, v_inst_4132_);
lean_closure_set(v___f_4138_, 1, v_msgData_4133_);
lean_closure_set(v___f_4138_, 2, v_toPure_4137_);
lean_closure_set(v___f_4138_, 3, v_toBind_4135_);
v___x_4139_ = lean_apply_4(v_toBind_4135_, lean_box(0), lean_box(0), v_getEnv_4136_, v___f_4138_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4140_, lean_object* v_inst_4141_, lean_object* v_inst_4142_, lean_object* v_inst_4143_, lean_object* v_msgData_4144_){
_start:
{
lean_object* v___x_4145_; 
v___x_4145_ = l_Lean_addMessageContextPartial___redArg(v_inst_4141_, v_inst_4142_, v_inst_4143_, v_msgData_4144_);
return v___x_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4146_, lean_object* v_mctx_4147_, lean_object* v_lctx_4148_, lean_object* v_msgData_4149_, lean_object* v_toPure_4150_, lean_object* v_opts_4151_){
_start:
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4152_, 0, v_env_4146_);
lean_ctor_set(v___x_4152_, 1, v_mctx_4147_);
lean_ctor_set(v___x_4152_, 2, v_lctx_4148_);
lean_ctor_set(v___x_4152_, 3, v_opts_4151_);
v___x_4153_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
lean_ctor_set(v___x_4153_, 1, v_msgData_4149_);
v___x_4154_ = lean_apply_2(v_toPure_4150_, lean_box(0), v___x_4153_);
return v___x_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_inst_4155_, lean_object* v_env_4156_, lean_object* v_mctx_4157_, lean_object* v_msgData_4158_, lean_object* v_toPure_4159_, lean_object* v_toBind_4160_, lean_object* v_lctx_4161_){
_start:
{
lean_object* v_getOptionsUnrestricted_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; 
v_getOptionsUnrestricted_4162_ = lean_ctor_get(v_inst_4155_, 1);
lean_inc(v_getOptionsUnrestricted_4162_);
lean_dec_ref(v_inst_4155_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4163_, 0, v_env_4156_);
lean_closure_set(v___f_4163_, 1, v_mctx_4157_);
lean_closure_set(v___f_4163_, 2, v_lctx_4161_);
lean_closure_set(v___f_4163_, 3, v_msgData_4158_);
lean_closure_set(v___f_4163_, 4, v_toPure_4159_);
v___x_4164_ = lean_apply_4(v_toBind_4160_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4162_, v___f_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_inst_4165_, lean_object* v_env_4166_, lean_object* v_msgData_4167_, lean_object* v_toPure_4168_, lean_object* v_toBind_4169_, lean_object* v_inst_4170_, lean_object* v_mctx_4171_){
_start:
{
lean_object* v___f_4172_; lean_object* v___x_4173_; 
lean_inc(v_toBind_4169_);
v___f_4172_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4172_, 0, v_inst_4165_);
lean_closure_set(v___f_4172_, 1, v_env_4166_);
lean_closure_set(v___f_4172_, 2, v_mctx_4171_);
lean_closure_set(v___f_4172_, 3, v_msgData_4167_);
lean_closure_set(v___f_4172_, 4, v_toPure_4168_);
lean_closure_set(v___f_4172_, 5, v_toBind_4169_);
v___x_4173_ = lean_apply_4(v_toBind_4169_, lean_box(0), lean_box(0), v_inst_4170_, v___f_4172_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4174_, lean_object* v_inst_4175_, lean_object* v_msgData_4176_, lean_object* v_toPure_4177_, lean_object* v_toBind_4178_, lean_object* v_inst_4179_, lean_object* v_____do__lift_4180_){
_start:
{
lean_object* v_getMCtx_4181_; uint8_t v___x_4182_; lean_object* v_env_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; 
v_getMCtx_4181_ = lean_ctor_get(v_inst_4174_, 0);
lean_inc(v_getMCtx_4181_);
lean_dec_ref(v_inst_4174_);
v___x_4182_ = 0;
v_env_4183_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4180_, v___x_4182_);
lean_inc(v_toBind_4178_);
v___f_4184_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4184_, 0, v_inst_4175_);
lean_closure_set(v___f_4184_, 1, v_env_4183_);
lean_closure_set(v___f_4184_, 2, v_msgData_4176_);
lean_closure_set(v___f_4184_, 3, v_toPure_4177_);
lean_closure_set(v___f_4184_, 4, v_toBind_4178_);
lean_closure_set(v___f_4184_, 5, v_inst_4179_);
v___x_4185_ = lean_apply_4(v_toBind_4178_, lean_box(0), lean_box(0), v_getMCtx_4181_, v___f_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4186_, lean_object* v_inst_4187_, lean_object* v_inst_4188_, lean_object* v_inst_4189_, lean_object* v_inst_4190_, lean_object* v_msgData_4191_){
_start:
{
lean_object* v_toApplicative_4192_; lean_object* v_toBind_4193_; lean_object* v_getEnv_4194_; lean_object* v_toPure_4195_; lean_object* v___f_4196_; lean_object* v___x_4197_; 
v_toApplicative_4192_ = lean_ctor_get(v_inst_4186_, 0);
lean_inc_ref(v_toApplicative_4192_);
v_toBind_4193_ = lean_ctor_get(v_inst_4186_, 1);
lean_inc_n(v_toBind_4193_, 2);
lean_dec_ref(v_inst_4186_);
v_getEnv_4194_ = lean_ctor_get(v_inst_4187_, 0);
lean_inc(v_getEnv_4194_);
lean_dec_ref(v_inst_4187_);
v_toPure_4195_ = lean_ctor_get(v_toApplicative_4192_, 1);
lean_inc(v_toPure_4195_);
lean_dec_ref(v_toApplicative_4192_);
v___f_4196_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4196_, 0, v_inst_4188_);
lean_closure_set(v___f_4196_, 1, v_inst_4190_);
lean_closure_set(v___f_4196_, 2, v_msgData_4191_);
lean_closure_set(v___f_4196_, 3, v_toPure_4195_);
lean_closure_set(v___f_4196_, 4, v_toBind_4193_);
lean_closure_set(v___f_4196_, 5, v_inst_4189_);
v___x_4197_ = lean_apply_4(v_toBind_4193_, lean_box(0), lean_box(0), v_getEnv_4194_, v___f_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_inst_4201_, lean_object* v_inst_4202_, lean_object* v_inst_4203_, lean_object* v_msgData_4204_){
_start:
{
lean_object* v___x_4205_; 
v___x_4205_ = l_Lean_addMessageContextFull___redArg(v_inst_4199_, v_inst_4200_, v_inst_4201_, v_inst_4202_, v_inst_4203_, v_msgData_4204_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg(){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0));
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object* v___dummy_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v_res_4211_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4213_){
_start:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4215_);
lean_dec_ref(v_s_4215_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4217_, lean_object* v___x_4218_, lean_object* v___x_4219_, lean_object* v_a_4220_, lean_object* v_b_4221_){
_start:
{
lean_object* v_it_4223_; lean_object* v_startInclusive_4224_; lean_object* v_endExclusive_4225_; 
if (lean_obj_tag(v_a_4220_) == 0)
{
lean_object* v_currPos_4231_; lean_object* v_searcher_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4255_; 
v_currPos_4231_ = lean_ctor_get(v_a_4220_, 0);
v_searcher_4232_ = lean_ctor_get(v_a_4220_, 1);
v_isSharedCheck_4255_ = !lean_is_exclusive(v_a_4220_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4234_ = v_a_4220_;
v_isShared_4235_ = v_isSharedCheck_4255_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_searcher_4232_);
lean_inc(v_currPos_4231_);
lean_dec(v_a_4220_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4255_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
uint8_t v_decide_4236_; 
v_decide_4236_ = lean_nat_dec_eq(v_searcher_4232_, v___x_4219_);
if (v_decide_4236_ == 0)
{
uint32_t v___x_4237_; uint32_t v___x_4238_; uint8_t v___x_4239_; 
v___x_4237_ = 10;
v___x_4238_ = lean_string_utf8_get_fast(v_str_4217_, v_searcher_4232_);
v___x_4239_ = lean_uint32_dec_eq(v___x_4238_, v___x_4237_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; lean_object* v___x_4242_; 
v___x_4240_ = lean_string_utf8_next_fast(v_str_4217_, v_searcher_4232_);
lean_dec(v_searcher_4232_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___x_4240_);
v___x_4242_ = v___x_4234_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_currPos_4231_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
v_a_4220_ = v___x_4242_;
goto _start;
}
}
else
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v_slice_4248_; lean_object* v_nextIt_4250_; 
v___x_4245_ = lean_string_utf8_next_fast(v_str_4217_, v_searcher_4232_);
v___x_4246_ = lean_nat_sub(v___x_4245_, v_searcher_4232_);
v___x_4247_ = lean_nat_add(v_searcher_4232_, v___x_4246_);
lean_dec(v___x_4246_);
v_slice_4248_ = l_String_Slice_subslice_x21(v___x_4218_, v_currPos_4231_, v_searcher_4232_);
lean_inc(v___x_4247_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___x_4247_);
lean_ctor_set(v___x_4234_, 0, v___x_4247_);
v_nextIt_4250_ = v___x_4234_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4253_, 1, v___x_4247_);
v_nextIt_4250_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v_startInclusive_4251_; lean_object* v_endExclusive_4252_; 
v_startInclusive_4251_ = lean_ctor_get(v_slice_4248_, 0);
lean_inc(v_startInclusive_4251_);
v_endExclusive_4252_ = lean_ctor_get(v_slice_4248_, 1);
lean_inc(v_endExclusive_4252_);
lean_dec_ref(v_slice_4248_);
v_it_4223_ = v_nextIt_4250_;
v_startInclusive_4224_ = v_startInclusive_4251_;
v_endExclusive_4225_ = v_endExclusive_4252_;
goto v___jp_4222_;
}
}
}
else
{
lean_object* v___x_4254_; 
lean_del_object(v___x_4234_);
lean_dec(v_searcher_4232_);
v___x_4254_ = lean_box(1);
lean_inc(v___x_4219_);
v_it_4223_ = v___x_4254_;
v_startInclusive_4224_ = v_currPos_4231_;
v_endExclusive_4225_ = v___x_4219_;
goto v___jp_4222_;
}
}
}
else
{
lean_dec(v___x_4219_);
return v_b_4221_;
}
v___jp_4222_:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4226_ = lean_string_utf8_extract_fast(v_str_4217_, v_startInclusive_4224_, v_endExclusive_4225_);
lean_dec(v_endExclusive_4225_);
lean_dec(v_startInclusive_4224_);
v___x_4227_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
v___x_4228_ = l_Lean_MessageData_ofFormat(v___x_4227_);
v___x_4229_ = lean_array_push(v_b_4221_, v___x_4228_);
v_a_4220_ = v_it_4223_;
v_b_4221_ = v___x_4229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4256_, lean_object* v___x_4257_, lean_object* v___x_4258_, lean_object* v_a_4259_, lean_object* v_b_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4256_, v___x_4257_, v___x_4258_, v_a_4259_, v_b_4260_);
lean_dec_ref(v___x_4257_);
lean_dec_ref(v_str_4256_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4264_){
_start:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v_lines_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4265_ = lean_unsigned_to_nat(0u);
v___x_4266_ = lean_string_utf8_byte_size(v_str_4264_);
lean_inc_ref(v_str_4264_);
v___x_4267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4267_, 0, v_str_4264_);
lean_ctor_set(v___x_4267_, 1, v___x_4265_);
lean_ctor_set(v___x_4267_, 2, v___x_4266_);
v_lines_4268_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
v___x_4269_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4264_, v___x_4267_, v___x_4266_, v_lines_4268_, v___x_4269_);
lean_dec_ref_known(v___x_4267_, 3);
lean_dec_ref(v_str_4264_);
v___x_4271_ = lean_array_to_list(v___x_4270_);
v___x_4272_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4273_ = l_Lean_MessageData_joinSep(v___x_4271_, v___x_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4274_, lean_object* v___x_4275_, lean_object* v___x_4276_, lean_object* v_inst_4277_, lean_object* v_R_4278_, lean_object* v_a_4279_, lean_object* v_b_4280_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4274_, v___x_4275_, v___x_4276_, v_a_4279_, v_b_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v_inst_4285_, lean_object* v_R_4286_, lean_object* v_a_4287_, lean_object* v_b_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4282_, v___x_4283_, v___x_4284_, v_inst_4285_, v_R_4286_, v_a_4287_, v_b_4288_);
lean_dec_ref(v___x_4283_);
lean_dec_ref(v_str_4282_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4290_){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4292_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4292_, 0, lean_box(0));
lean_closure_set(v___x_4292_, 1, lean_box(0));
lean_closure_set(v___x_4292_, 2, lean_box(0));
lean_closure_set(v___x_4292_, 3, v___x_4291_);
lean_closure_set(v___x_4292_, 4, v_inst_4290_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4293_, lean_object* v_inst_4294_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg(){
_start:
{
lean_object* v___f_4303_; 
v___f_4303_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object* v___dummy_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_instToMessageDataTSyntax___redArg();
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4306_){
_start:
{
lean_object* v___f_4307_; 
v___f_4307_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l_Lean_instToMessageDataTSyntax(v_k_4308_);
lean_dec(v_k_4308_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4314_, lean_object* v_as_4315_){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4316_ = lean_box(0);
v___x_4317_ = l_List_mapTR_loop___redArg(v_inst_4314_, v_as_4315_, v___x_4316_);
v___x_4318_ = l_Lean_MessageData_ofList(v___x_4317_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4319_){
_start:
{
lean_object* v___f_4320_; 
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4320_, 0, v_inst_4319_);
return v___f_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4321_, lean_object* v_inst_4322_){
_start:
{
lean_object* v___f_4323_; 
v___f_4323_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4323_, 0, v_inst_4322_);
return v___f_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4324_, lean_object* v_as_4325_){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4326_ = lean_array_to_list(v_as_4325_);
v___x_4327_ = lean_box(0);
v___x_4328_ = l_List_mapTR_loop___redArg(v_inst_4324_, v___x_4326_, v___x_4327_);
v___x_4329_ = l_Lean_MessageData_ofList(v___x_4328_);
return v___x_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4330_){
_start:
{
lean_object* v___f_4331_; 
v___f_4331_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4331_, 0, v_inst_4330_);
return v___f_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4332_, lean_object* v_inst_4333_){
_start:
{
lean_object* v___f_4334_; 
v___f_4334_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4334_, 0, v_inst_4333_);
return v___f_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4335_, lean_object* v_acc_4336_, lean_object* v_recur_4337_){
_start:
{
lean_object* v_array_4338_; lean_object* v_start_4339_; lean_object* v_stop_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4353_; 
v_array_4338_ = lean_ctor_get(v_it_4335_, 0);
v_start_4339_ = lean_ctor_get(v_it_4335_, 1);
v_stop_4340_ = lean_ctor_get(v_it_4335_, 2);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_it_4335_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4342_ = v_it_4335_;
v_isShared_4343_ = v_isSharedCheck_4353_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_stop_4340_);
lean_inc(v_start_4339_);
lean_inc(v_array_4338_);
lean_dec(v_it_4335_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4353_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_nat_dec_lt(v_start_4339_, v_stop_4340_);
if (v___x_4344_ == 0)
{
lean_del_object(v___x_4342_);
lean_dec(v_stop_4340_);
lean_dec(v_start_4339_);
lean_dec_ref(v_array_4338_);
lean_dec_ref(v_recur_4337_);
return v_acc_4336_;
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4348_; 
v___x_4345_ = lean_unsigned_to_nat(1u);
v___x_4346_ = lean_nat_add(v_start_4339_, v___x_4345_);
lean_inc_ref(v_array_4338_);
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 1, v___x_4346_);
v___x_4348_ = v___x_4342_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_array_4338_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v_stop_4340_);
v___x_4348_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = lean_array_fget(v_array_4338_, v_start_4339_);
lean_dec(v_start_4339_);
lean_dec_ref(v_array_4338_);
v___x_4350_ = lean_array_push(v_acc_4336_, v___x_4349_);
v___x_4351_ = lean_apply_3(v_recur_4337_, v___x_4348_, v___x_4350_, lean_box(0));
return v___x_4351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4356_, lean_object* v_inst_4357_, lean_object* v_as_4358_){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4359_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4360_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4356_, v_as_4358_, v___x_4359_);
v___x_4361_ = lean_array_to_list(v___x_4360_);
v___x_4362_ = lean_box(0);
v___x_4363_ = l_List_mapTR_loop___redArg(v_inst_4357_, v___x_4361_, v___x_4362_);
v___x_4364_ = l_Lean_MessageData_ofList(v___x_4363_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4366_){
_start:
{
lean_object* v___f_4367_; lean_object* v___f_4368_; 
v___f_4367_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4368_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4368_, 0, v___f_4367_);
lean_closure_set(v___f_4368_, 1, v_inst_4366_);
return v___f_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4369_, lean_object* v_inst_4370_){
_start:
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4370_);
return v___x_4371_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4376_ = l_Lean_MessageData_ofFormat(v___x_4375_);
return v___x_4376_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4380_ = l_Lean_MessageData_ofFormat(v___x_4379_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4381_, lean_object* v_x_4382_){
_start:
{
if (lean_obj_tag(v_x_4382_) == 0)
{
lean_object* v___x_4383_; 
lean_dec_ref(v_inst_4381_);
v___x_4383_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4383_;
}
else
{
lean_object* v_val_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v_val_4384_ = lean_ctor_get(v_x_4382_, 0);
lean_inc(v_val_4384_);
lean_dec_ref_known(v_x_4382_, 1);
v___x_4385_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4386_ = lean_apply_1(v_inst_4381_, v_val_4384_);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
return v___x_4389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4390_){
_start:
{
lean_object* v___f_4391_; 
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4391_, 0, v_inst_4390_);
return v___f_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4392_, lean_object* v_inst_4393_){
_start:
{
lean_object* v___f_4394_; 
v___f_4394_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4394_, 0, v_inst_4393_);
return v___f_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4395_, lean_object* v_inst_4396_, lean_object* v_x_4397_){
_start:
{
lean_object* v_fst_4398_; lean_object* v_snd_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4413_; 
v_fst_4398_ = lean_ctor_get(v_x_4397_, 0);
v_snd_4399_ = lean_ctor_get(v_x_4397_, 1);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_x_4397_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4401_ = v_x_4397_;
v_isShared_4402_ = v_isSharedCheck_4413_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_snd_4399_);
lean_inc(v_fst_4398_);
lean_dec(v_x_4397_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4413_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4403_ = lean_apply_1(v_inst_4395_, v_fst_4398_);
v___x_4404_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 7);
lean_ctor_set(v___x_4401_, 1, v___x_4404_);
lean_ctor_set(v___x_4401_, 0, v___x_4403_);
v___x_4406_ = v___x_4401_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4412_, 1, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4407_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = lean_apply_1(v_inst_4396_, v_snd_4399_);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l_Lean_MessageData_paren(v___x_4410_);
return v___x_4411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4414_, lean_object* v_inst_4415_){
_start:
{
lean_object* v___f_4416_; 
v___f_4416_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4416_, 0, v_inst_4414_);
lean_closure_set(v___f_4416_, 1, v_inst_4415_);
return v___f_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4417_, lean_object* v_00_u03b2_4418_, lean_object* v_inst_4419_, lean_object* v_inst_4420_){
_start:
{
lean_object* v___f_4421_; 
v___f_4421_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4421_, 0, v_inst_4419_);
lean_closure_set(v___f_4421_, 1, v_inst_4420_);
return v___f_4421_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4426_ = l_Lean_MessageData_ofFormat(v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4427_){
_start:
{
if (lean_obj_tag(v_x_4427_) == 0)
{
lean_object* v___x_4428_; 
v___x_4428_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4428_;
}
else
{
lean_object* v_val_4429_; lean_object* v___x_4430_; 
v_val_4429_ = lean_ctor_get(v_x_4427_, 0);
lean_inc(v_val_4429_);
lean_dec_ref_known(v_x_4427_, 1);
v___x_4430_ = l_Lean_MessageData_ofExpr(v_val_4429_);
return v___x_4430_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4464_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4465_ = l_String_toRawSubstring_x27(v___x_4464_);
return v___x_4465_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4481_ = l_String_toRawSubstring_x27(v___x_4480_);
return v___x_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_){
_start:
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4495_);
v___x_4499_ = l_Lean_Syntax_isOfKind(v_x_4495_, v___x_4498_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
lean_dec(v_x_4495_);
v___x_4500_ = lean_box(1);
v___x_4501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4500_);
lean_ctor_set(v___x_4501_, 1, v_a_4497_);
return v___x_4501_;
}
else
{
lean_object* v_quotContext_4502_; lean_object* v_currMacroScope_4503_; lean_object* v_ref_4504_; lean_object* v___x_4505_; lean_object* v_interpStr_4506_; uint8_t v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; 
v_quotContext_4502_ = lean_ctor_get(v_a_4496_, 1);
v_currMacroScope_4503_ = lean_ctor_get(v_a_4496_, 2);
v_ref_4504_ = lean_ctor_get(v_a_4496_, 5);
v___x_4505_ = lean_unsigned_to_nat(1u);
v_interpStr_4506_ = l_Lean_Syntax_getArg(v_x_4495_, v___x_4505_);
lean_dec(v_x_4495_);
v___x_4507_ = 0;
v___x_4508_ = l_Lean_SourceInfo_fromRef(v_ref_4504_, v___x_4507_);
v___x_4509_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4510_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4503_, 2);
lean_inc_n(v_quotContext_4502_, 2);
v___x_4511_ = l_Lean_addMacroScope(v_quotContext_4502_, v___x_4510_, v_currMacroScope_4503_);
v___x_4512_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4508_);
v___x_4513_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4508_);
lean_ctor_set(v___x_4513_, 1, v___x_4509_);
lean_ctor_set(v___x_4513_, 2, v___x_4511_);
lean_ctor_set(v___x_4513_, 3, v___x_4512_);
v___x_4514_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4515_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4516_ = l_Lean_addMacroScope(v_quotContext_4502_, v___x_4515_, v_currMacroScope_4503_);
v___x_4517_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4508_);
lean_ctor_set(v___x_4518_, 1, v___x_4514_);
lean_ctor_set(v___x_4518_, 2, v___x_4516_);
lean_ctor_set(v___x_4518_, 3, v___x_4517_);
lean_inc_ref(v___x_4518_);
v___x_4519_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4506_, v___x_4513_, v___x_4518_, v___x_4518_, v_a_4496_, v_a_4497_);
lean_dec(v_interpStr_4506_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
v_a_4521_ = lean_ctor_get(v___x_4519_, 1);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4519_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_inc(v_a_4520_);
lean_dec(v___x_4519_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4520_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
v_a_4529_ = lean_ctor_get(v___x_4519_, 0);
v_a_4530_ = lean_ctor_get(v___x_4519_, 1);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4519_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_inc(v_a_4529_);
lean_dec(v___x_4519_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4529_);
lean_ctor_set(v_reuseFailAlloc_4536_, 1, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4538_, v_a_4539_, v_a_4540_);
lean_dec_ref(v_a_4539_);
return v_res_4541_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4544_ = l_Lean_stringToMessageData(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4545_){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4546_ = lean_array_to_list(v_msgs_4545_);
v___x_4547_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4548_ = l_Lean_MessageData_joinSep(v___x_4546_, v___x_4547_);
v___x_4549_ = l_Lean_indentD(v___x_4548_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4550_, lean_object* v_lctx_4551_, lean_object* v_opts_4552_, lean_object* v_msg_4553_){
_start:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4554_ = l_Lean_Environment_ofKernelEnv(v_env_4550_);
v___x_4555_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
lean_ctor_set(v___x_4556_, 2, v_lctx_4551_);
lean_ctor_set(v___x_4556_, 3, v_opts_4552_);
v___x_4557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
lean_ctor_set(v___x_4557_, 1, v_msg_4553_);
return v___x_4557_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4560_ = l_Lean_stringToMessageData(v___x_4559_);
return v___x_4560_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4562_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4563_ = l_Lean_stringToMessageData(v___x_4562_);
return v___x_4563_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
v___x_4565_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4566_ = l_Lean_stringToMessageData(v___x_4565_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4567_, lean_object* v_n_4568_, lean_object* v_expectedType_4569_){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4570_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4571_ = l_Lean_MessageData_ofName(v_n_4568_);
v___x_4572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4570_);
lean_ctor_set(v___x_4572_, 1, v___x_4571_);
v___x_4573_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
v___x_4575_ = l_Lean_indentExpr(v_givenType_4567_);
v___x_4576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4574_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
v___x_4577_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4576_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = l_Lean_indentExpr(v_expectedType_4569_);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4578_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
return v___x_4580_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
return v___x_4582_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4583_ = lean_box(1);
v___x_4584_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4585_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4586_, 0, v___x_4585_);
lean_ctor_set(v___x_4586_, 1, v___x_4584_);
lean_ctor_set(v___x_4586_, 2, v___x_4583_);
return v___x_4586_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__2));
v___x_4589_ = l_Lean_stringToMessageData(v___x_4588_);
return v___x_4589_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__4));
v___x_4592_ = l_Lean_stringToMessageData(v___x_4591_);
return v___x_4592_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__6));
v___x_4595_ = l_Lean_stringToMessageData(v___x_4594_);
return v___x_4595_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__9));
v___x_4600_ = l_Lean_MessageData_ofFormat(v___x_4599_);
return v___x_4600_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__12(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__11));
v___x_4603_ = l_Lean_stringToMessageData(v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__14(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__13));
v___x_4606_ = l_Lean_stringToMessageData(v___x_4605_);
return v___x_4606_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__16(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__15));
v___x_4609_ = l_Lean_stringToMessageData(v___x_4608_);
return v___x_4609_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__18(void){
_start:
{
lean_object* v___x_4611_; lean_object* v___x_4612_; 
v___x_4611_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__17));
v___x_4612_ = l_Lean_stringToMessageData(v___x_4611_);
return v___x_4612_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__20(void){
_start:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__19));
v___x_4615_ = l_Lean_stringToMessageData(v___x_4614_);
return v___x_4615_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__22(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__21));
v___x_4618_ = l_Lean_stringToMessageData(v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__24(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__23));
v___x_4621_ = l_Lean_stringToMessageData(v___x_4620_);
return v___x_4621_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__26(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__25));
v___x_4624_ = l_Lean_stringToMessageData(v___x_4623_);
return v___x_4624_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__28(void){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__27));
v___x_4627_ = l_Lean_stringToMessageData(v___x_4626_);
return v___x_4627_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__30(void){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__29));
v___x_4630_ = l_Lean_stringToMessageData(v___x_4629_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__32(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__31));
v___x_4633_ = l_Lean_stringToMessageData(v___x_4632_);
return v___x_4633_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__34(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__33));
v___x_4636_ = l_Lean_stringToMessageData(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__36(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__35));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__38(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__37));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__41(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__40));
v___x_4647_ = l_Lean_MessageData_ofFormat(v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__44(void){
_start:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___x_4651_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__43));
v___x_4652_ = l_Lean_MessageData_ofFormat(v___x_4651_);
return v___x_4652_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__47(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__46));
v___x_4657_ = l_Lean_MessageData_ofFormat(v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__50(void){
_start:
{
lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4661_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__49));
v___x_4662_ = l_Lean_MessageData_ofFormat(v___x_4661_);
return v___x_4662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4663_, lean_object* v_opts_4664_){
_start:
{
switch(lean_obj_tag(v_e_4663_))
{
case 0:
{
lean_object* v_env_4665_; lean_object* v_name_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4679_; 
v_env_4665_ = lean_ctor_get(v_e_4663_, 0);
v_name_4666_ = lean_ctor_get(v_e_4663_, 1);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_e_4663_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4668_ = v_e_4663_;
v_isShared_4669_ = v_isSharedCheck_4679_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_name_4666_);
lean_inc(v_env_4665_);
lean_dec(v_e_4663_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4679_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4674_; 
v___x_4670_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4671_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__3, &l_Lean_Kernel_Exception_toMessageData___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__3);
v___x_4672_ = l_Lean_MessageData_ofName(v_name_4666_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set_tag(v___x_4668_, 7);
lean_ctor_set(v___x_4668_, 1, v___x_4672_);
lean_ctor_set(v___x_4668_, 0, v___x_4671_);
v___x_4674_ = v___x_4668_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v___x_4672_);
v___x_4674_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4675_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4674_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
v___x_4677_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4665_, v___x_4670_, v_opts_4664_, v___x_4676_);
return v___x_4677_;
}
}
}
case 1:
{
lean_object* v_env_4680_; lean_object* v_name_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4695_; 
v_env_4680_ = lean_ctor_get(v_e_4663_, 0);
v_name_4681_ = lean_ctor_get(v_e_4663_, 1);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_e_4663_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4683_ = v_e_4663_;
v_isShared_4684_ = v_isSharedCheck_4695_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_name_4681_);
lean_inc(v_env_4680_);
lean_dec(v_e_4663_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4695_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
v___x_4685_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4686_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__7, &l_Lean_Kernel_Exception_toMessageData___closed__7_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__7);
v___x_4687_ = 1;
v___x_4688_ = l_Lean_MessageData_ofConstName(v_name_4681_, v___x_4687_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 7);
lean_ctor_set(v___x_4683_, 1, v___x_4688_);
lean_ctor_set(v___x_4683_, 0, v___x_4686_);
v___x_4690_ = v___x_4683_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4694_, 1, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4691_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4680_, v___x_4685_, v_opts_4664_, v___x_4692_);
return v___x_4693_;
}
}
}
case 2:
{
lean_object* v_env_4696_; lean_object* v_decl_4697_; lean_object* v_givenType_4698_; lean_object* v___x_4699_; 
v_env_4696_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4696_);
v_decl_4697_ = lean_ctor_get(v_e_4663_, 1);
lean_inc(v_decl_4697_);
v_givenType_4698_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_givenType_4698_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4699_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
switch(lean_obj_tag(v_decl_4697_))
{
case 1:
{
lean_object* v_val_4700_; lean_object* v_toConstantVal_4701_; lean_object* v_name_4702_; lean_object* v_type_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v_val_4700_ = lean_ctor_get(v_decl_4697_, 0);
lean_inc_ref(v_val_4700_);
lean_dec_ref_known(v_decl_4697_, 1);
v_toConstantVal_4701_ = lean_ctor_get(v_val_4700_, 0);
lean_inc_ref(v_toConstantVal_4701_);
lean_dec_ref(v_val_4700_);
v_name_4702_ = lean_ctor_get(v_toConstantVal_4701_, 0);
lean_inc(v_name_4702_);
v_type_4703_ = lean_ctor_get(v_toConstantVal_4701_, 2);
lean_inc_ref(v_type_4703_);
lean_dec_ref(v_toConstantVal_4701_);
v___x_4704_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4698_, v_name_4702_, v_type_4703_);
v___x_4705_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4696_, v___x_4699_, v_opts_4664_, v___x_4704_);
return v___x_4705_;
}
case 2:
{
lean_object* v_val_4706_; lean_object* v_toConstantVal_4707_; lean_object* v_name_4708_; lean_object* v_type_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v_val_4706_ = lean_ctor_get(v_decl_4697_, 0);
lean_inc_ref(v_val_4706_);
lean_dec_ref_known(v_decl_4697_, 1);
v_toConstantVal_4707_ = lean_ctor_get(v_val_4706_, 0);
lean_inc_ref(v_toConstantVal_4707_);
lean_dec_ref(v_val_4706_);
v_name_4708_ = lean_ctor_get(v_toConstantVal_4707_, 0);
lean_inc(v_name_4708_);
v_type_4709_ = lean_ctor_get(v_toConstantVal_4707_, 2);
lean_inc_ref(v_type_4709_);
lean_dec_ref(v_toConstantVal_4707_);
v___x_4710_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4698_, v_name_4708_, v_type_4709_);
v___x_4711_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4696_, v___x_4699_, v_opts_4664_, v___x_4710_);
return v___x_4711_;
}
default: 
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
lean_dec_ref(v_givenType_4698_);
lean_dec(v_decl_4697_);
v___x_4712_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__10, &l_Lean_Kernel_Exception_toMessageData___closed__10_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__10);
v___x_4713_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4696_, v___x_4699_, v_opts_4664_, v___x_4712_);
return v___x_4713_;
}
}
}
case 3:
{
lean_object* v_env_4714_; lean_object* v_name_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v_env_4714_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4714_);
v_name_4715_ = lean_ctor_get(v_e_4663_, 1);
lean_inc(v_name_4715_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4716_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4717_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__12, &l_Lean_Kernel_Exception_toMessageData___closed__12_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__12);
v___x_4718_ = 1;
v___x_4719_ = l_Lean_MessageData_ofConstName(v_name_4715_, v___x_4718_);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4717_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4720_);
lean_ctor_set(v___x_4722_, 1, v___x_4721_);
v___x_4723_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4714_, v___x_4716_, v_opts_4664_, v___x_4722_);
return v___x_4723_;
}
case 4:
{
lean_object* v_env_4724_; lean_object* v_name_4725_; lean_object* v_expr_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v_env_4724_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4724_);
v_name_4725_ = lean_ctor_get(v_e_4663_, 1);
lean_inc(v_name_4725_);
v_expr_4726_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_expr_4726_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4727_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4728_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__14, &l_Lean_Kernel_Exception_toMessageData___closed__14_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__14);
v___x_4729_ = 1;
v___x_4730_ = l_Lean_MessageData_ofConstName(v_name_4725_, v___x_4729_);
v___x_4731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4728_);
lean_ctor_set(v___x_4731_, 1, v___x_4730_);
v___x_4732_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__16, &l_Lean_Kernel_Exception_toMessageData___closed__16_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__16);
v___x_4733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4731_);
lean_ctor_set(v___x_4733_, 1, v___x_4732_);
v___x_4734_ = l_Lean_indentExpr(v_expr_4726_);
v___x_4735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4735_, 0, v___x_4733_);
lean_ctor_set(v___x_4735_, 1, v___x_4734_);
v___x_4736_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4724_, v___x_4727_, v_opts_4664_, v___x_4735_);
return v___x_4736_;
}
case 5:
{
lean_object* v_env_4737_; lean_object* v_lctx_4738_; lean_object* v_expr_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_env_4737_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4737_);
v_lctx_4738_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4738_);
v_expr_4739_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_expr_4739_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4740_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__18, &l_Lean_Kernel_Exception_toMessageData___closed__18_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__18);
v___x_4741_ = l_Lean_indentExpr(v_expr_4739_);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4737_, v_lctx_4738_, v_opts_4664_, v___x_4742_);
return v___x_4743_;
}
case 6:
{
lean_object* v_env_4744_; lean_object* v_lctx_4745_; lean_object* v_expr_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
v_env_4744_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4744_);
v_lctx_4745_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4745_);
v_expr_4746_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_expr_4746_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4747_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__20, &l_Lean_Kernel_Exception_toMessageData___closed__20_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__20);
v___x_4748_ = l_Lean_indentExpr(v_expr_4746_);
v___x_4749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4747_);
lean_ctor_set(v___x_4749_, 1, v___x_4748_);
v___x_4750_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4744_, v_lctx_4745_, v_opts_4664_, v___x_4749_);
return v___x_4750_;
}
case 7:
{
lean_object* v_env_4751_; lean_object* v_lctx_4752_; lean_object* v_name_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_env_4751_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4751_);
v_lctx_4752_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4752_);
v_name_4753_ = lean_ctor_get(v_e_4663_, 2);
lean_inc(v_name_4753_);
lean_dec_ref_known(v_e_4663_, 5);
v___x_4754_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__22, &l_Lean_Kernel_Exception_toMessageData___closed__22_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__22);
v___x_4755_ = l_Lean_MessageData_ofName(v_name_4753_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4754_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4751_, v_lctx_4752_, v_opts_4664_, v___x_4758_);
return v___x_4759_;
}
case 8:
{
lean_object* v_env_4760_; lean_object* v_lctx_4761_; lean_object* v_expr_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v_env_4760_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4760_);
v_lctx_4761_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4761_);
v_expr_4762_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_expr_4762_);
lean_dec_ref_known(v_e_4663_, 4);
v___x_4763_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__24, &l_Lean_Kernel_Exception_toMessageData___closed__24_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__24);
v___x_4764_ = l_Lean_indentExpr(v_expr_4762_);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4763_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4760_, v_lctx_4761_, v_opts_4664_, v___x_4765_);
return v___x_4766_;
}
case 9:
{
lean_object* v_env_4767_; lean_object* v_lctx_4768_; lean_object* v_app_4769_; lean_object* v_funType_4770_; lean_object* v_argType_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_env_4767_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4767_);
v_lctx_4768_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4768_);
v_app_4769_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_app_4769_);
v_funType_4770_ = lean_ctor_get(v_e_4663_, 3);
lean_inc_ref(v_funType_4770_);
v_argType_4771_ = lean_ctor_get(v_e_4663_, 4);
lean_inc_ref(v_argType_4771_);
lean_dec_ref_known(v_e_4663_, 5);
v___x_4772_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__26, &l_Lean_Kernel_Exception_toMessageData___closed__26_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__26);
v___x_4773_ = l_Lean_indentExpr(v_app_4769_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__28, &l_Lean_Kernel_Exception_toMessageData___closed__28_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__28);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_indentExpr(v_argType_4771_);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
v___x_4779_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__30, &l_Lean_Kernel_Exception_toMessageData___closed__30_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__30);
v___x_4780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4778_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = l_Lean_indentExpr(v_funType_4770_);
v___x_4782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4780_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
v___x_4783_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4767_, v_lctx_4768_, v_opts_4664_, v___x_4782_);
return v___x_4783_;
}
case 10:
{
lean_object* v_env_4784_; lean_object* v_lctx_4785_; lean_object* v_proj_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v_env_4784_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4784_);
v_lctx_4785_ = lean_ctor_get(v_e_4663_, 1);
lean_inc_ref(v_lctx_4785_);
v_proj_4786_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_proj_4786_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4787_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__32, &l_Lean_Kernel_Exception_toMessageData___closed__32_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__32);
v___x_4788_ = l_Lean_indentExpr(v_proj_4786_);
v___x_4789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4784_, v_lctx_4785_, v_opts_4664_, v___x_4789_);
return v___x_4790_;
}
case 11:
{
lean_object* v_env_4791_; lean_object* v_name_4792_; lean_object* v_type_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; uint8_t v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_env_4791_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_env_4791_);
v_name_4792_ = lean_ctor_get(v_e_4663_, 1);
lean_inc(v_name_4792_);
v_type_4793_ = lean_ctor_get(v_e_4663_, 2);
lean_inc_ref(v_type_4793_);
lean_dec_ref_known(v_e_4663_, 3);
v___x_4794_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4795_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__34, &l_Lean_Kernel_Exception_toMessageData___closed__34_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__34);
v___x_4796_ = 1;
v___x_4797_ = l_Lean_MessageData_ofConstName(v_name_4792_, v___x_4796_);
v___x_4798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4795_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__36, &l_Lean_Kernel_Exception_toMessageData___closed__36_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__36);
v___x_4800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4798_);
lean_ctor_set(v___x_4800_, 1, v___x_4799_);
v___x_4801_ = l_Lean_indentExpr(v_type_4793_);
v___x_4802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4800_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
v___x_4803_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4791_, v___x_4794_, v_opts_4664_, v___x_4802_);
return v___x_4803_;
}
case 12:
{
lean_object* v_msg_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
lean_dec_ref(v_opts_4664_);
v_msg_4804_ = lean_ctor_get(v_e_4663_, 0);
lean_inc_ref(v_msg_4804_);
lean_dec_ref_known(v_e_4663_, 1);
v___x_4805_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__38, &l_Lean_Kernel_Exception_toMessageData___closed__38_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__38);
v___x_4806_ = l_Lean_stringToMessageData(v_msg_4804_);
v___x_4807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4805_);
lean_ctor_set(v___x_4807_, 1, v___x_4806_);
return v___x_4807_;
}
case 13:
{
lean_object* v___x_4808_; 
lean_dec_ref(v_opts_4664_);
v___x_4808_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__41, &l_Lean_Kernel_Exception_toMessageData___closed__41_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__41);
return v___x_4808_;
}
case 14:
{
lean_object* v___x_4809_; 
lean_dec_ref(v_opts_4664_);
v___x_4809_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__44, &l_Lean_Kernel_Exception_toMessageData___closed__44_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__44);
return v___x_4809_;
}
case 15:
{
lean_object* v___x_4810_; 
lean_dec_ref(v_opts_4664_);
v___x_4810_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__47, &l_Lean_Kernel_Exception_toMessageData___closed__47_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__47);
return v___x_4810_;
}
default: 
{
lean_object* v___x_4811_; 
lean_dec_ref(v_opts_4664_);
v___x_4811_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__50, &l_Lean_Kernel_Exception_toMessageData___closed__50_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__50);
return v___x_4811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4812_, lean_object* v_e_4813_, lean_object* v_cls_4814_){
_start:
{
lean_object* v___x_4815_; double v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4815_ = lean_box(0);
v___x_4816_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__7, &l_Lean_MessageData_formatAux___closed__7_once, _init_l_Lean_MessageData_formatAux___closed__7);
v___x_4817_ = 1;
v___x_4818_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4819_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4819_, 0, v_cls_4814_);
lean_ctor_set(v___x_4819_, 1, v___x_4815_);
lean_ctor_set(v___x_4819_, 2, v___x_4818_);
lean_ctor_set_float(v___x_4819_, sizeof(void*)*3, v___x_4816_);
lean_ctor_set_float(v___x_4819_, sizeof(void*)*3 + 8, v___x_4816_);
lean_ctor_set_uint8(v___x_4819_, sizeof(void*)*3 + 16, v___x_4817_);
v___x_4820_ = lean_apply_1(v_inst_4812_, v_e_4813_);
v___x_4821_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4822_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4819_);
lean_ctor_set(v___x_4822_, 1, v___x_4820_);
lean_ctor_set(v___x_4822_, 2, v___x_4821_);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4823_, lean_object* v_inst_4824_, lean_object* v_e_4825_, lean_object* v_cls_4826_){
_start:
{
lean_object* v___x_4827_; 
v___x_4827_ = l_Lean_toTraceElem___redArg(v_inst_4824_, v_e_4825_, v_cls_4826_);
return v___x_4827_;
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
