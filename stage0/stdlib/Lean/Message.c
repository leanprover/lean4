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
lean_object* l_Lean_MessageSeverity_ctorIdx___impl(uint8_t v_x_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_box(v_x_92_);
v___x_94_ = lean_obj_tag_nat(v___x_93_);
lean_dec(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_92_ = stack[0].m_num;
lean_object* v_res_95_;
v_res_95_ = l_Lean_MessageSeverity_ctorIdx___impl(v_x_92_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorIdx___impl___boxed(lean_object* v_x_96_){
_start:
{
uint8_t v_x_4__boxed_97_; lean_object* v_res_98_; 
v_x_4__boxed_97_ = lean_unbox(v_x_96_);
v_res_98_ = l_Lean_MessageSeverity_ctorIdx___impl(v_x_4__boxed_97_);
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
lean_object* l_Lean_MessageSeverity_ctorElim(lean_object* v_motive_102_, lean_object* v_ctorIdx_103_, uint8_t v_t_104_, lean_object* v_h_105_, lean_object* v_k_106_){
_start:
{
lean_inc(v_k_106_);
return v_k_106_;
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_103_ = stack[1].m_obj;
uint8_t v_t_104_ = stack[2].m_num;
lean_object* v_k_106_ = stack[4].m_obj;
lean_object* v_res_107_;
v_res_107_ = l_Lean_MessageSeverity_ctorElim(lean_box(0), v_ctorIdx_103_, v_t_104_, lean_box(0), v_k_106_);
stack->m_obj
 = v_res_107_;
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_ctorElim___boxed(lean_object* v_motive_108_, lean_object* v_ctorIdx_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_k_112_){
_start:
{
uint8_t v_t_boxed_113_; lean_object* v_res_114_; 
v_t_boxed_113_ = lean_unbox(v_t_110_);
v_res_114_ = l_Lean_MessageSeverity_ctorElim(v_motive_108_, v_ctorIdx_109_, v_t_boxed_113_, v_h_111_, v_k_112_);
lean_dec(v_k_112_);
lean_dec(v_ctorIdx_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg(lean_object* v_information_115_){
_start:
{
lean_inc(v_information_115_);
return v_information_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___redArg___boxed(lean_object* v_information_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_MessageSeverity_information_elim___redArg(v_information_116_);
lean_dec(v_information_116_);
return v_res_117_;
}
}
lean_object* l_Lean_MessageSeverity_information_elim(lean_object* v_motive_118_, uint8_t v_t_119_, lean_object* v_h_120_, lean_object* v_information_121_){
_start:
{
lean_inc(v_information_121_);
return v_information_121_;
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_information_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_119_ = stack[1].m_num;
lean_object* v_information_121_ = stack[3].m_obj;
lean_object* v_res_122_;
v_res_122_ = l_Lean_MessageSeverity_information_elim(lean_box(0), v_t_119_, lean_box(0), v_information_121_);
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_information_elim___boxed(lean_object* v_motive_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_information_126_){
_start:
{
uint8_t v_t_boxed_127_; lean_object* v_res_128_; 
v_t_boxed_127_ = lean_unbox(v_t_124_);
v_res_128_ = l_Lean_MessageSeverity_information_elim(v_motive_123_, v_t_boxed_127_, v_h_125_, v_information_126_);
lean_dec(v_information_126_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg(lean_object* v_warning_129_){
_start:
{
lean_inc(v_warning_129_);
return v_warning_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_warning_elim___redArg___boxed(lean_object* v_warning_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_MessageSeverity_warning_elim___redArg(v_warning_130_);
lean_dec(v_warning_130_);
return v_res_131_;
}
}
lean_object* l_Lean_MessageSeverity_warning_elim(lean_object* v_motive_132_, uint8_t v_t_133_, lean_object* v_h_134_, lean_object* v_warning_135_){
_start:
{
lean_inc(v_warning_135_);
return v_warning_135_;
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_warning_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_133_ = stack[1].m_num;
lean_object* v_warning_135_ = stack[3].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_MessageSeverity_warning_elim(lean_box(0), v_t_133_, lean_box(0), v_warning_135_);
stack->m_obj
 = v_res_136_;
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
lean_object* l_Lean_MessageSeverity_error_elim(lean_object* v_motive_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_error_149_){
_start:
{
lean_inc(v_error_149_);
return v_error_149_;
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_error_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_147_ = stack[1].m_num;
lean_object* v_error_149_ = stack[3].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_MessageSeverity_error_elim(lean_box(0), v_t_147_, lean_box(0), v_error_149_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_error_elim___boxed(lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_error_154_){
_start:
{
uint8_t v_t_boxed_155_; lean_object* v_res_156_; 
v_t_boxed_155_ = lean_unbox(v_t_152_);
v_res_156_ = l_Lean_MessageSeverity_error_elim(v_motive_151_, v_t_boxed_155_, v_h_153_, v_error_154_);
lean_dec(v_error_154_);
return v_res_156_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity_default(void){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
static uint8_t _init_l_Lean_instInhabitedMessageSeverity(void){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t v_x_159_, uint8_t v_y_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_161_ = lean_box(v_x_159_);
v___x_162_ = lean_obj_tag_nat(v___x_161_);
lean_dec(v___x_161_);
v___x_163_ = lean_box(v_y_160_);
v___x_164_ = lean_obj_tag_nat(v___x_163_);
lean_dec(v___x_163_);
v___x_165_ = lean_nat_dec_eq(v___x_162_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT void l_Lean_instBEqMessageSeverity_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_159_ = stack[0].m_num;
uint8_t v_y_160_ = stack[1].m_num;
uint8_t v_res_166_;
v_res_166_ = l_Lean_instBEqMessageSeverity_beq(v_x_159_, v_y_160_);
stack->m_num = v_res_166_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqMessageSeverity_beq___boxed(lean_object* v_x_167_, lean_object* v_y_168_){
_start:
{
uint8_t v_x_24__boxed_169_; uint8_t v_y_25__boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_x_24__boxed_169_ = lean_unbox(v_x_167_);
v_y_25__boxed_170_ = lean_unbox(v_y_168_);
v_res_171_ = l_Lean_instBEqMessageSeverity_beq(v_x_24__boxed_169_, v_y_25__boxed_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
lean_object* l_Lean_instToJsonMessageSeverity_toJson(uint8_t v_x_184_){
_start:
{
switch(v_x_184_)
{
case 0:
{
lean_object* v___x_185_; 
v___x_185_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__1));
return v___x_185_;
}
case 1:
{
lean_object* v___x_186_; 
v___x_186_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__3));
return v___x_186_;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__5));
return v___x_187_;
}
}
}
}
LEAN_EXPORT void l_Lean_instToJsonMessageSeverity_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_184_ = stack[0].m_num;
lean_object* v_res_188_;
v_res_188_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_184_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_instToJsonMessageSeverity_toJson___boxed(lean_object* v_x_189_){
_start:
{
uint8_t v_x_67__boxed_190_; lean_object* v_res_191_; 
v_x_67__boxed_190_ = lean_unbox(v_x_189_);
v_res_191_ = l_Lean_instToJsonMessageSeverity_toJson(v_x_67__boxed_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonMessageSeverity_fromJson(lean_object* v_json_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Json_getTag_x3f(v_json_209_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__1));
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___x_213_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
v___x_214_ = lean_string_dec_eq(v_val_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
v___x_216_ = lean_string_dec_eq(v_val_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
v___x_218_ = lean_string_dec_eq(v_val_212_, v___x_217_);
lean_dec(v_val_212_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; 
v___x_219_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__3));
return v___x_219_;
}
else
{
lean_object* v___x_220_; 
v___x_220_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__4));
return v___x_220_;
}
}
else
{
lean_object* v___x_221_; 
lean_dec(v_val_212_);
v___x_221_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__5));
return v___x_221_;
}
}
else
{
lean_object* v___x_222_; 
lean_dec(v_val_212_);
v___x_222_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity_fromJson___closed__6));
return v___x_222_;
}
}
}
}
lean_object* l_Lean_MessageSeverity_toString(uint8_t v_x_225_){
_start:
{
switch(v_x_225_)
{
case 0:
{
lean_object* v___x_226_; 
v___x_226_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__0));
return v___x_226_;
}
case 1:
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__2));
return v___x_227_;
}
default: 
{
lean_object* v___x_228_; 
v___x_228_ = ((lean_object*)(l_Lean_instToJsonMessageSeverity_toJson___closed__4));
return v___x_228_;
}
}
}
}
LEAN_EXPORT void l_Lean_MessageSeverity_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_225_ = stack[0].m_num;
lean_object* v_res_229_;
v_res_229_ = l_Lean_MessageSeverity_toString(v_x_225_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_MessageSeverity_toString___boxed(lean_object* v_x_230_){
_start:
{
uint8_t v_x_28__boxed_231_; lean_object* v_res_232_; 
v_x_28__boxed_231_ = lean_unbox(v_x_230_);
v_res_232_ = l_Lean_MessageSeverity_toString(v_x_28__boxed_231_);
return v_res_232_;
}
}
lean_object* l_Lean_TraceResult_ctorIdx___impl(uint8_t v_x_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_box(v_x_235_);
v___x_237_ = lean_obj_tag_nat(v___x_236_);
lean_dec(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Lean_TraceResult_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_235_ = stack[0].m_num;
lean_object* v_res_238_;
v_res_238_ = l_Lean_TraceResult_ctorIdx___impl(v_x_235_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorIdx___impl___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_x_4__boxed_240_; lean_object* v_res_241_; 
v_x_4__boxed_240_ = lean_unbox(v_x_239_);
v_res_241_ = l_Lean_TraceResult_ctorIdx___impl(v_x_4__boxed_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg(lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___redArg___boxed(lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_TraceResult_ctorElim___redArg(v_k_243_);
lean_dec(v_k_243_);
return v_res_244_;
}
}
lean_object* l_Lean_TraceResult_ctorElim(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT void l_Lean_TraceResult_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_246_ = stack[1].m_obj;
uint8_t v_t_247_ = stack[2].m_num;
lean_object* v_k_249_ = stack[4].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lean_TraceResult_ctorElim(lean_box(0), v_ctorIdx_246_, v_t_247_, lean_box(0), v_k_249_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_ctorElim___boxed(lean_object* v_motive_251_, lean_object* v_ctorIdx_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_k_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_TraceResult_ctorElim(v_motive_251_, v_ctorIdx_252_, v_t_boxed_256_, v_h_254_, v_k_255_);
lean_dec(v_k_255_);
lean_dec(v_ctorIdx_252_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg(lean_object* v_success_258_){
_start:
{
lean_inc(v_success_258_);
return v_success_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___redArg___boxed(lean_object* v_success_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_TraceResult_success_elim___redArg(v_success_259_);
lean_dec(v_success_259_);
return v_res_260_;
}
}
lean_object* l_Lean_TraceResult_success_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_success_264_){
_start:
{
lean_inc(v_success_264_);
return v_success_264_;
}
}
LEAN_EXPORT void l_Lean_TraceResult_success_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_262_ = stack[1].m_num;
lean_object* v_success_264_ = stack[3].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_TraceResult_success_elim(lean_box(0), v_t_262_, lean_box(0), v_success_264_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_success_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_success_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_TraceResult_success_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_success_269_);
lean_dec(v_success_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg(lean_object* v_failure_272_){
_start:
{
lean_inc(v_failure_272_);
return v_failure_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___redArg___boxed(lean_object* v_failure_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_TraceResult_failure_elim___redArg(v_failure_273_);
lean_dec(v_failure_273_);
return v_res_274_;
}
}
lean_object* l_Lean_TraceResult_failure_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_failure_278_){
_start:
{
lean_inc(v_failure_278_);
return v_failure_278_;
}
}
LEAN_EXPORT void l_Lean_TraceResult_failure_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_276_ = stack[1].m_num;
lean_object* v_failure_278_ = stack[3].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_TraceResult_failure_elim(lean_box(0), v_t_276_, lean_box(0), v_failure_278_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_failure_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_failure_283_){
_start:
{
uint8_t v_t_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_284_ = lean_unbox(v_t_281_);
v_res_285_ = l_Lean_TraceResult_failure_elim(v_motive_280_, v_t_boxed_284_, v_h_282_, v_failure_283_);
lean_dec(v_failure_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg(lean_object* v_error_286_){
_start:
{
lean_inc(v_error_286_);
return v_error_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___redArg___boxed(lean_object* v_error_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_TraceResult_error_elim___redArg(v_error_287_);
lean_dec(v_error_287_);
return v_res_288_;
}
}
lean_object* l_Lean_TraceResult_error_elim(lean_object* v_motive_289_, uint8_t v_t_290_, lean_object* v_h_291_, lean_object* v_error_292_){
_start:
{
lean_inc(v_error_292_);
return v_error_292_;
}
}
LEAN_EXPORT void l_Lean_TraceResult_error_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_290_ = stack[1].m_num;
lean_object* v_error_292_ = stack[3].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_TraceResult_error_elim(lean_box(0), v_t_290_, lean_box(0), v_error_292_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_error_elim___boxed(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_error_297_){
_start:
{
uint8_t v_t_boxed_298_; lean_object* v_res_299_; 
v_t_boxed_298_ = lean_unbox(v_t_295_);
v_res_299_ = l_Lean_TraceResult_error_elim(v_motive_294_, v_t_boxed_298_, v_h_296_, v_error_297_);
lean_dec(v_error_297_);
return v_res_299_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult_default(void){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
static uint8_t _init_l_Lean_instInhabitedTraceResult(void){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = 0;
return v___x_301_;
}
}
uint8_t l_Lean_instBEqTraceResult_beq(uint8_t v_x_302_, uint8_t v_y_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_304_ = lean_box(v_x_302_);
v___x_305_ = lean_obj_tag_nat(v___x_304_);
lean_dec(v___x_304_);
v___x_306_ = lean_box(v_y_303_);
v___x_307_ = lean_obj_tag_nat(v___x_306_);
lean_dec(v___x_306_);
v___x_308_ = lean_nat_dec_eq(v___x_305_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_instBEqTraceResult_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_302_ = stack[0].m_num;
uint8_t v_y_303_ = stack[1].m_num;
uint8_t v_res_309_;
v_res_309_ = l_Lean_instBEqTraceResult_beq(v_x_302_, v_y_303_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqTraceResult_beq___boxed(lean_object* v_x_310_, lean_object* v_y_311_){
_start:
{
uint8_t v_x_24__boxed_312_; uint8_t v_y_25__boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_x_24__boxed_312_ = lean_unbox(v_x_310_);
v_y_25__boxed_313_ = lean_unbox(v_y_311_);
v_res_314_ = l_Lean_instBEqTraceResult_beq(v_x_24__boxed_312_, v_y_25__boxed_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__6(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(2u);
v___x_328_ = lean_nat_to_int(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_instReprTraceResult_repr___closed__7(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_to_int(v___x_329_);
return v___x_330_;
}
}
lean_object* l_Lean_instReprTraceResult_repr(uint8_t v_x_331_, lean_object* v_prec_332_){
_start:
{
lean_object* v___y_334_; lean_object* v___y_341_; lean_object* v___y_348_; 
switch(v_x_331_)
{
case 0:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1024u);
v___x_355_ = lean_nat_dec_le(v___x_354_, v_prec_332_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_334_ = v___x_356_;
goto v___jp_333_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_334_ = v___x_357_;
goto v___jp_333_;
}
}
case 1:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = lean_unsigned_to_nat(1024u);
v___x_359_ = lean_nat_dec_le(v___x_358_, v_prec_332_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_341_ = v___x_360_;
goto v___jp_340_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_341_ = v___x_361_;
goto v___jp_340_;
}
}
default: 
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(1024u);
v___x_363_ = lean_nat_dec_le(v___x_362_, v_prec_332_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___y_348_ = v___x_364_;
goto v___jp_347_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__7, &l_Lean_instReprTraceResult_repr___closed__7_once, _init_l_Lean_instReprTraceResult_repr___closed__7);
v___y_348_ = v___x_365_;
goto v___jp_347_;
}
}
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__1));
lean_inc(v___y_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_332_);
return v___x_339_;
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_342_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__3));
lean_inc(v___y_341_);
v___x_343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_343_, 0, v___y_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = 0;
v___x_345_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*1, v___x_344_);
v___x_346_ = l_Repr_addAppParen(v___x_345_, v_prec_332_);
return v___x_346_;
}
v___jp_347_:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_349_ = ((lean_object*)(l_Lean_instReprTraceResult_repr___closed__5));
lean_inc(v___y_348_);
v___x_350_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_350_, 0, v___y_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = 0;
v___x_352_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1, v___x_351_);
v___x_353_ = l_Repr_addAppParen(v___x_352_, v_prec_332_);
return v___x_353_;
}
}
}
LEAN_EXPORT void l_Lean_instReprTraceResult_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_331_ = stack[0].m_num;
lean_object* v_prec_332_ = stack[1].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_instReprTraceResult_repr(v_x_331_, v_prec_332_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_instReprTraceResult_repr___boxed(lean_object* v_x_367_, lean_object* v_prec_368_){
_start:
{
uint8_t v_x_171__boxed_369_; lean_object* v_res_370_; 
v_x_171__boxed_369_ = lean_unbox(v_x_367_);
v_res_370_ = l_Lean_instReprTraceResult_repr(v_x_171__boxed_369_, v_prec_368_);
lean_dec(v_prec_368_);
return v_res_370_;
}
}
lean_object* l_Lean_TraceResult_toEmoji(uint8_t v_x_376_){
_start:
{
switch(v_x_376_)
{
case 0:
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__0));
return v___x_377_;
}
case 1:
{
lean_object* v___x_378_; 
v___x_378_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__1));
return v___x_378_;
}
default: 
{
lean_object* v___x_379_; 
v___x_379_ = ((lean_object*)(l_Lean_TraceResult_toEmoji___closed__2));
return v___x_379_;
}
}
}
}
LEAN_EXPORT void l_Lean_TraceResult_toEmoji_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_376_ = stack[0].m_num;
lean_object* v_res_380_;
v_res_380_ = l_Lean_TraceResult_toEmoji(v_x_376_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_TraceResult_toEmoji___boxed(lean_object* v_x_381_){
_start:
{
uint8_t v_x_31__boxed_382_; lean_object* v_res_383_; 
v_x_31__boxed_382_ = lean_unbox(v_x_381_);
v_res_383_ = l_Lean_TraceResult_toEmoji(v_x_31__boxed_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl(lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_obj_tag_nat(v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorIdx___impl___boxed(lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_MessageData_ctorIdx___impl(v_x_386_);
lean_dec_ref(v_x_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___redArg(lean_object* v_t_388_, lean_object* v_k_389_){
_start:
{
switch(lean_obj_tag(v_t_388_))
{
case 0:
{
lean_object* v_a_390_; lean_object* v___x_391_; 
v_a_390_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_a_390_);
lean_dec_ref_known(v_t_388_, 1);
v___x_391_ = lean_apply_1(v_k_389_, v_a_390_);
return v___x_391_;
}
case 1:
{
lean_object* v_a_392_; lean_object* v___x_393_; 
v_a_392_ = lean_ctor_get(v_t_388_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v_t_388_, 1);
v___x_393_ = lean_apply_1(v_k_389_, v_a_392_);
return v___x_393_;
}
case 5:
{
lean_object* v_a_394_; lean_object* v_a_395_; lean_object* v___x_396_; 
v_a_394_ = lean_ctor_get(v_t_388_, 0);
lean_inc(v_a_394_);
v_a_395_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_a_395_);
lean_dec_ref_known(v_t_388_, 2);
v___x_396_ = lean_apply_2(v_k_389_, v_a_394_, v_a_395_);
return v___x_396_;
}
case 6:
{
lean_object* v_a_397_; lean_object* v___x_398_; 
v_a_397_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_a_397_);
lean_dec_ref_known(v_t_388_, 1);
v___x_398_ = lean_apply_1(v_k_389_, v_a_397_);
return v___x_398_;
}
case 8:
{
lean_object* v_a_399_; lean_object* v_a_400_; lean_object* v___x_401_; 
v_a_399_ = lean_ctor_get(v_t_388_, 0);
lean_inc(v_a_399_);
v_a_400_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_a_400_);
lean_dec_ref_known(v_t_388_, 2);
v___x_401_ = lean_apply_2(v_k_389_, v_a_399_, v_a_400_);
return v___x_401_;
}
case 9:
{
lean_object* v_data_402_; lean_object* v_msg_403_; lean_object* v_children_404_; lean_object* v___x_405_; 
v_data_402_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_data_402_);
v_msg_403_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_msg_403_);
v_children_404_ = lean_ctor_get(v_t_388_, 2);
lean_inc_ref(v_children_404_);
lean_dec_ref_known(v_t_388_, 3);
v___x_405_ = lean_apply_3(v_k_389_, v_data_402_, v_msg_403_, v_children_404_);
return v___x_405_;
}
case 11:
{
lean_object* v_a_406_; lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_406_ = lean_ctor_get(v_t_388_, 0);
lean_inc(v_a_406_);
v_a_407_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_a_407_);
lean_dec_ref_known(v_t_388_, 2);
v___x_408_ = lean_apply_2(v_k_389_, v_a_406_, v_a_407_);
return v___x_408_;
}
default: 
{
lean_object* v_a_409_; lean_object* v_a_410_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v_t_388_, 0);
lean_inc_ref(v_a_409_);
v_a_410_ = lean_ctor_get(v_t_388_, 1);
lean_inc_ref(v_a_410_);
lean_dec_ref(v_t_388_);
v___x_411_ = lean_apply_2(v_k_389_, v_a_409_, v_a_410_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim(lean_object* v_motive__1_412_, lean_object* v_ctorIdx_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_k_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_MessageData_ctorElim___redArg(v_t_414_, v_k_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ctorElim___boxed(lean_object* v_motive__1_418_, lean_object* v_ctorIdx_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_k_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_MessageData_ctorElim(v_motive__1_418_, v_ctorIdx_419_, v_t_420_, v_h_421_, v_k_422_);
lean_dec(v_ctorIdx_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim___redArg(lean_object* v_t_424_, lean_object* v_ofFormatWithInfos_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_MessageData_ctorElim___redArg(v_t_424_, v_ofFormatWithInfos_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfos_elim(lean_object* v_motive__1_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_ofFormatWithInfos_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_MessageData_ctorElim___redArg(v_t_428_, v_ofFormatWithInfos_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim___redArg(lean_object* v_t_432_, lean_object* v_ofGoal_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MessageData_ctorElim___redArg(v_t_432_, v_ofGoal_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofGoal_elim(lean_object* v_motive__1_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_ofGoal_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MessageData_ctorElim___redArg(v_t_436_, v_ofGoal_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim___redArg(lean_object* v_t_440_, lean_object* v_ofWidget_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_MessageData_ctorElim___redArg(v_t_440_, v_ofWidget_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofWidget_elim(lean_object* v_motive__1_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_ofWidget_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_MessageData_ctorElim___redArg(v_t_444_, v_ofWidget_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim___redArg(lean_object* v_t_448_, lean_object* v_withContext_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_MessageData_ctorElim___redArg(v_t_448_, v_withContext_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withContext_elim(lean_object* v_motive__1_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_withContext_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MessageData_ctorElim___redArg(v_t_452_, v_withContext_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim___redArg(lean_object* v_t_456_, lean_object* v_withNamingContext_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MessageData_ctorElim___redArg(v_t_456_, v_withNamingContext_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withNamingContext_elim(lean_object* v_motive__1_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_withNamingContext_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_MessageData_ctorElim___redArg(v_t_460_, v_withNamingContext_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim___redArg(lean_object* v_t_464_, lean_object* v_nest_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_MessageData_ctorElim___redArg(v_t_464_, v_nest_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nest_elim(lean_object* v_motive__1_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_nest_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_MessageData_ctorElim___redArg(v_t_468_, v_nest_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim___redArg(lean_object* v_t_472_, lean_object* v_group_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_MessageData_ctorElim___redArg(v_t_472_, v_group_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_group_elim(lean_object* v_motive__1_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_group_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_MessageData_ctorElim___redArg(v_t_476_, v_group_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim___redArg(lean_object* v_t_480_, lean_object* v_compose_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MessageData_ctorElim___redArg(v_t_480_, v_compose_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_compose_elim(lean_object* v_motive__1_483_, lean_object* v_t_484_, lean_object* v_h_485_, lean_object* v_compose_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_MessageData_ctorElim___redArg(v_t_484_, v_compose_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim___redArg(lean_object* v_t_488_, lean_object* v_tagged_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_MessageData_ctorElim___redArg(v_t_488_, v_tagged_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagged_elim(lean_object* v_motive__1_491_, lean_object* v_t_492_, lean_object* v_h_493_, lean_object* v_tagged_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_MessageData_ctorElim___redArg(v_t_492_, v_tagged_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim___redArg(lean_object* v_t_496_, lean_object* v_trace_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_MessageData_ctorElim___redArg(v_t_496_, v_trace_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_trace_elim(lean_object* v_motive__1_499_, lean_object* v_t_500_, lean_object* v_h_501_, lean_object* v_trace_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_MessageData_ctorElim___redArg(v_t_500_, v_trace_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim___redArg(lean_object* v_t_504_, lean_object* v_ofLazy_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_MessageData_ctorElim___redArg(v_t_504_, v_ofLazy_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazy_elim(lean_object* v_motive__1_507_, lean_object* v_t_508_, lean_object* v_h_509_, lean_object* v_ofLazy_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_MessageData_ctorElim___redArg(v_t_508_, v_ofLazy_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim___redArg(lean_object* v_t_512_, lean_object* v_ofOriginatingSyntax_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_MessageData_ctorElim___redArg(v_t_512_, v_ofOriginatingSyntax_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofOriginatingSyntax_elim(lean_object* v_motive__1_515_, lean_object* v_t_516_, lean_object* v_h_517_, lean_object* v_ofOriginatingSyntax_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_MessageData_ctorElim___redArg(v_t_516_, v_ofOriginatingSyntax_518_);
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
lean_object* l_Lean_MessageData_lazy___lam__0(lean_object* v___x_535_, lean_object* v_onMissingContext_536_, lean_object* v_f_537_, lean_object* v_ctx_x3f_538_){
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
LEAN_EXPORT void l_Lean_MessageData_lazy___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_535_ = stack[0].m_obj;
lean_object* v_onMissingContext_536_ = stack[1].m_obj;
lean_object* v_f_537_ = stack[2].m_obj;
lean_object* v_ctx_x3f_538_ = stack[3].m_obj;
lean_object* v_res_547_;
v_res_547_ = l_Lean_MessageData_lazy___lam__0(v___x_535_, v_onMissingContext_536_, v_f_537_, v_ctx_x3f_538_);
stack->m_obj
 = v_res_547_;
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
v___x_557_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
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
uint8_t l_Lean_MessageData_hasTag(lean_object* v_p_560_, lean_object* v_x_561_){
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
return v___x_589_;
}
else
{
if (v___x_589_ == 0)
{
lean_dec_ref(v_children_582_);
lean_dec_ref(v_p_560_);
return v___x_589_;
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
LEAN_EXPORT void l_Lean_MessageData_hasTag_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_560_ = stack[0].m_obj;
lean_object* v_x_561_ = stack[1].m_obj;
uint8_t v_res_597_;
v_res_597_ = l_Lean_MessageData_hasTag(v_p_560_, v_x_561_);
stack->m_num = v_res_597_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(lean_object* v_p_598_, lean_object* v_as_599_, size_t v_i_600_, size_t v_stop_601_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_598_ = stack[0].m_obj;
lean_object* v_as_599_ = stack[1].m_obj;
size_t v_i_600_ = stack[2].m_num;
size_t v_stop_601_ = stack[3].m_num;
uint8_t v_res_609_;
v_res_609_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_598_, v_as_599_, v_i_600_, v_stop_601_);
stack->m_num = v_res_609_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0___boxed(lean_object* v_p_610_, lean_object* v_as_611_, lean_object* v_i_612_, lean_object* v_stop_613_){
_start:
{
size_t v_i_boxed_614_; size_t v_stop_boxed_615_; uint8_t v_res_616_; lean_object* v_r_617_; 
v_i_boxed_614_ = lean_unbox_usize(v_i_612_);
lean_dec(v_i_612_);
v_stop_boxed_615_ = lean_unbox_usize(v_stop_613_);
lean_dec(v_stop_613_);
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_MessageData_hasTag_spec__0(v_p_610_, v_as_611_, v_i_boxed_614_, v_stop_boxed_615_);
lean_dec_ref(v_as_611_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasTag___boxed(lean_object* v_p_618_, lean_object* v_x_619_){
_start:
{
uint8_t v_res_620_; lean_object* v_r_621_; 
v_res_620_ = l_Lean_MessageData_hasTag(v_p_618_, v_x_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind(lean_object* v_x_622_){
_start:
{
switch(lean_obj_tag(v_x_622_))
{
case 3:
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v_x_622_, 1);
v_x_622_ = v_a_623_;
goto _start;
}
case 4:
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v_x_622_, 1);
v_x_622_ = v_a_625_;
goto _start;
}
case 8:
{
lean_object* v_a_627_; 
v_a_627_ = lean_ctor_get(v_x_622_, 0);
lean_inc(v_a_627_);
return v_a_627_;
}
case 9:
{
lean_object* v_data_628_; lean_object* v_cls_629_; 
v_data_628_ = lean_ctor_get(v_x_622_, 0);
v_cls_629_ = lean_ctor_get(v_data_628_, 0);
lean_inc(v_cls_629_);
return v_cls_629_;
}
case 11:
{
lean_object* v_a_630_; 
v_a_630_ = lean_ctor_get(v_x_622_, 1);
v_x_622_ = v_a_630_;
goto _start;
}
default: 
{
lean_object* v___x_632_; 
v___x_632_ = lean_box(0);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_kind___boxed(lean_object* v_x_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_MessageData_kind(v_x_633_);
lean_dec_ref(v_x_633_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_originatingSyntax_x3f(lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 11)
{
lean_object* v_a_636_; lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_645_; 
v_a_636_ = lean_ctor_get(v_x_635_, 0);
v_a_637_ = lean_ctor_get(v_x_635_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_639_ = v_x_635_;
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_inc(v_a_636_);
lean_dec(v_x_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_645_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_641_, 0, v_a_636_);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 0);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_a_637_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_box(0);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_x_635_);
return v___x_647_;
}
}
}
uint8_t l_Lean_MessageData_isTrace(lean_object* v_x_648_){
_start:
{
switch(lean_obj_tag(v_x_648_))
{
case 3:
{
lean_object* v_a_649_; 
v_a_649_ = lean_ctor_get(v_x_648_, 1);
v_x_648_ = v_a_649_;
goto _start;
}
case 4:
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v_x_648_, 1);
v_x_648_ = v_a_651_;
goto _start;
}
case 8:
{
lean_object* v_a_653_; 
v_a_653_ = lean_ctor_get(v_x_648_, 1);
v_x_648_ = v_a_653_;
goto _start;
}
case 9:
{
uint8_t v___x_655_; 
v___x_655_ = 1;
return v___x_655_;
}
case 11:
{
lean_object* v_a_656_; 
v_a_656_ = lean_ctor_get(v_x_648_, 1);
v_x_648_ = v_a_656_;
goto _start;
}
default: 
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
}
}
LEAN_EXPORT void l_Lean_MessageData_isTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_648_ = stack[0].m_obj;
uint8_t v_res_659_;
v_res_659_ = l_Lean_MessageData_isTrace(v_x_648_);
stack->m_num = v_res_659_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isTrace___boxed(lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Lean_MessageData_isTrace(v_x_660_);
lean_dec_ref(v_x_660_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_composePreservingKind(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
switch(lean_obj_tag(v_x_663_))
{
case 3:
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_674_; 
v_a_665_ = lean_ctor_get(v_x_663_, 0);
v_a_666_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_674_ == 0)
{
v___x_668_ = v_x_663_;
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v_x_663_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_674_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_MessageData_composePreservingKind(v_a_666_, v_x_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_665_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
case 4:
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_a_675_ = lean_ctor_get(v_x_663_, 0);
v_a_676_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v_x_663_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v_x_663_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = l_Lean_MessageData_composePreservingKind(v_a_676_, v_x_664_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___x_680_);
v___x_682_ = v___x_678_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(4, 2, 0);
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
case 8:
{
lean_object* v_a_685_; lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
v_a_685_ = lean_ctor_get(v_x_663_, 0);
v_a_686_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_694_ == 0)
{
v___x_688_ = v_x_663_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_inc(v_a_685_);
lean_dec(v_x_663_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 7);
lean_ctor_set(v___x_688_, 1, v_x_664_);
lean_ctor_set(v___x_688_, 0, v_a_686_);
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_686_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_x_664_);
v___x_691_ = v_reuseFailAlloc_693_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_692_; 
v___x_692_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_692_, 0, v_a_685_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
return v___x_692_;
}
}
}
case 11:
{
lean_object* v_a_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_704_; 
v_a_695_ = lean_ctor_get(v_x_663_, 0);
v_a_696_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_704_ == 0)
{
v___x_698_ = v_x_663_;
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_inc(v_a_695_);
lean_dec(v_x_663_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_704_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_MessageData_composePreservingKind(v_a_696_, v_x_664_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_700_);
v___x_702_ = v___x_698_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_695_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
default: 
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v_x_663_);
lean_ctor_set(v___x_705_, 1, v_x_664_);
return v___x_705_;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_nil___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_box(0);
v___x_707_ = l_Lean_MessageData_ofFormat(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_MessageData_nil(void){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext(lean_object* v_nCtx_709_, lean_object* v_ctx_710_){
_start:
{
lean_object* v_env_711_; lean_object* v_mctx_712_; lean_object* v_lctx_713_; lean_object* v_opts_714_; lean_object* v_currNamespace_715_; lean_object* v_openDecls_716_; lean_object* v___x_717_; 
v_env_711_ = lean_ctor_get(v_ctx_710_, 0);
v_mctx_712_ = lean_ctor_get(v_ctx_710_, 1);
v_lctx_713_ = lean_ctor_get(v_ctx_710_, 2);
v_opts_714_ = lean_ctor_get(v_ctx_710_, 3);
v_currNamespace_715_ = lean_ctor_get(v_nCtx_709_, 0);
v_openDecls_716_ = lean_ctor_get(v_nCtx_709_, 1);
lean_inc(v_openDecls_716_);
lean_inc(v_currNamespace_715_);
lean_inc_ref(v_opts_714_);
lean_inc_ref(v_lctx_713_);
lean_inc_ref(v_mctx_712_);
lean_inc_ref(v_env_711_);
v___x_717_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_717_, 0, v_env_711_);
lean_ctor_set(v___x_717_, 1, v_mctx_712_);
lean_ctor_set(v___x_717_, 2, v_lctx_713_);
lean_ctor_set(v___x_717_, 3, v_opts_714_);
lean_ctor_set(v___x_717_, 4, v_currNamespace_715_);
lean_ctor_set(v___x_717_, 5, v_openDecls_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_mkPPContext___boxed(lean_object* v_nCtx_718_, lean_object* v_ctx_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_MessageData_mkPPContext(v_nCtx_718_, v_ctx_719_);
lean_dec_ref(v_ctx_719_);
lean_dec_ref(v_nCtx_718_);
return v_res_720_;
}
}
uint8_t l_Lean_MessageData_ofSyntax___lam__0(lean_object* v_x_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = 0;
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_MessageData_ofSyntax___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_721_ = stack[0].m_obj;
uint8_t v_res_723_;
v_res_723_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_721_);
stack->m_num = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__0___boxed(lean_object* v_x_724_){
_start:
{
uint8_t v_res_725_; lean_object* v_r_726_; 
v_res_725_ = l_Lean_MessageData_ofSyntax___lam__0(v_x_724_);
lean_dec_ref(v_x_724_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
lean_object* l_Lean_MessageData_ofSyntax___lam__1(lean_object* v___x_727_, lean_object* v_stx_728_, lean_object* v_ctx_x3f_729_){
_start:
{
lean_object* v_val_732_; 
if (lean_obj_tag(v_ctx_x3f_729_) == 0)
{
lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = 0;
v___x_737_ = l_Lean_Syntax_formatStx(v_stx_728_, v___x_735_, v___x_736_);
v_val_732_ = v___x_737_;
goto v___jp_731_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v_ctx_x3f_729_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v_ctx_x3f_729_, 1);
v___x_739_ = l_Lean_ppTerm(v_val_738_, v_stx_728_);
v_val_732_ = v___x_739_;
goto v___jp_731_;
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = l_Lean_MessageData_ofFormat(v_val_732_);
v___x_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_727_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
return v___x_734_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_ofSyntax___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_727_ = stack[0].m_obj;
lean_object* v_stx_728_ = stack[1].m_obj;
lean_object* v_ctx_x3f_729_ = stack[2].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_727_, v_stx_728_, v_ctx_x3f_729_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax___lam__1___boxed(lean_object* v___x_741_, lean_object* v_stx_742_, lean_object* v_ctx_x3f_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_MessageData_ofSyntax___lam__1(v___x_741_, v_stx_742_, v_ctx_x3f_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofSyntax(lean_object* v_stx_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_stx_751_; lean_object* v___f_752_; lean_object* v___x_753_; 
v___f_748_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_749_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_750_ = lean_box(0);
v_stx_751_ = l_Lean_Syntax_copyHeadTailInfoFrom(v_stx_747_, v___x_750_);
v___f_752_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofSyntax___lam__1___boxed), 4, 2);
lean_closure_set(v___f_752_, 0, v___x_749_);
lean_closure_set(v___f_752_, 1, v_stx_751_);
v___x_753_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_753_, 0, v___f_752_);
lean_ctor_set(v___x_753_, 1, v___f_748_);
return v___x_753_;
}
}
uint8_t l_Lean_MessageData_ofExpr___lam__0(lean_object* v_e_754_, lean_object* v_mctx_755_){
_start:
{
lean_object* v___x_756_; lean_object* v_fst_757_; uint8_t v___x_758_; 
v___x_756_ = l_Lean_instantiateMVarsCore(v_mctx_755_, v_e_754_);
v_fst_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_fst_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = l_Lean_Expr_hasSyntheticSorry(v_fst_757_);
lean_dec(v_fst_757_);
return v___x_758_;
}
}
LEAN_EXPORT void l_Lean_MessageData_ofExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_754_ = stack[0].m_obj;
lean_object* v_mctx_755_ = stack[1].m_obj;
uint8_t v_res_759_;
v_res_759_ = l_Lean_MessageData_ofExpr___lam__0(v_e_754_, v_mctx_755_);
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__0___boxed(lean_object* v_e_760_, lean_object* v_mctx_761_){
_start:
{
uint8_t v_res_762_; lean_object* v_r_763_; 
v_res_762_ = l_Lean_MessageData_ofExpr___lam__0(v_e_760_, v_mctx_761_);
v_r_763_ = lean_box(v_res_762_);
return v_r_763_;
}
}
lean_object* l_Lean_MessageData_ofExpr___lam__1(lean_object* v___x_764_, lean_object* v_e_765_, lean_object* v_ctx_x3f_766_){
_start:
{
lean_object* v_val_769_; 
if (lean_obj_tag(v_ctx_x3f_766_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = lean_expr_dbg_to_string(v_e_765_);
lean_dec_ref(v_e_765_);
v___x_773_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = lean_box(1);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v_val_769_ = v___x_775_;
goto v___jp_768_;
}
else
{
lean_object* v_val_776_; lean_object* v___x_777_; 
v_val_776_ = lean_ctor_get(v_ctx_x3f_766_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_ctx_x3f_766_, 1);
v___x_777_ = l_Lean_ppExprWithInfos(v_val_776_, v_e_765_);
v_val_769_ = v___x_777_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_val_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_764_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
return v___x_771_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_ofExpr___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_764_ = stack[0].m_obj;
lean_object* v_e_765_ = stack[1].m_obj;
lean_object* v_ctx_x3f_766_ = stack[2].m_obj;
lean_object* v_res_778_;
v_res_778_ = l_Lean_MessageData_ofExpr___lam__1(v___x_764_, v_e_765_, v_ctx_x3f_766_);
stack->m_obj
 = v_res_778_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr___lam__1___boxed(lean_object* v___x_779_, lean_object* v_e_780_, lean_object* v_ctx_x3f_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_MessageData_ofExpr___lam__1(v___x_779_, v_e_780_, v_ctx_x3f_781_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofExpr(lean_object* v_e_784_){
_start:
{
lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___x_788_; 
lean_inc_ref(v_e_784_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_785_, 0, v_e_784_);
v___x_786_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_787_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__1___boxed), 4, 2);
lean_closure_set(v___f_787_, 0, v___x_786_);
lean_closure_set(v___f_787_, 1, v_e_784_);
v___x_788_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_788_, 0, v___f_787_);
lean_ctor_set(v___x_788_, 1, v___f_785_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0(lean_object* v_x_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__0___boxed(lean_object* v_x_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_MessageData_ofLevel___lam__0(v_x_791_);
lean_dec(v_x_791_);
return v_res_792_;
}
}
lean_object* l_Lean_MessageData_ofLevel___lam__2(lean_object* v___x_793_, lean_object* v_l_794_, lean_object* v___f_795_, lean_object* v_ctx_x3f_796_){
_start:
{
lean_object* v_val_799_; 
if (lean_obj_tag(v_ctx_x3f_796_) == 0)
{
uint8_t v___x_802_; lean_object* v___x_803_; 
v___x_802_ = 1;
v___x_803_ = l_Lean_Level_format(v_l_794_, v___x_802_, v___f_795_);
v_val_799_ = v___x_803_;
goto v___jp_798_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_805_; 
lean_dec_ref(v___f_795_);
v_val_804_ = lean_ctor_get(v_ctx_x3f_796_, 0);
lean_inc(v_val_804_);
lean_dec_ref_known(v_ctx_x3f_796_, 1);
v___x_805_ = l_Lean_ppLevel(v_val_804_, v_l_794_);
v_val_799_ = v___x_805_;
goto v___jp_798_;
}
v___jp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = l_Lean_MessageData_ofFormat(v_val_799_);
v___x_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_793_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
return v___x_801_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_ofLevel___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_793_ = stack[0].m_obj;
lean_object* v_l_794_ = stack[1].m_obj;
lean_object* v___f_795_ = stack[2].m_obj;
lean_object* v_ctx_x3f_796_ = stack[3].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_MessageData_ofLevel___lam__2(v___x_793_, v_l_794_, v___f_795_, v_ctx_x3f_796_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel___lam__2___boxed(lean_object* v___x_807_, lean_object* v_l_808_, lean_object* v___f_809_, lean_object* v_ctx_x3f_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_MessageData_ofLevel___lam__2(v___x_807_, v_l_808_, v___f_809_, v_ctx_x3f_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLevel(lean_object* v_l_814_){
_start:
{
lean_object* v___f_815_; lean_object* v___f_816_; lean_object* v___x_817_; lean_object* v___f_818_; lean_object* v___x_819_; 
v___f_815_ = ((lean_object*)(l_Lean_MessageData_ofLevel___closed__0));
v___f_816_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_817_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___f_818_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofLevel___lam__2___boxed), 5, 3);
lean_closure_set(v___f_818_, 0, v___x_817_);
lean_closure_set(v___f_818_, 1, v_l_814_);
lean_closure_set(v___f_818_, 2, v___f_815_);
v___x_819_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_819_, 0, v___f_818_);
lean_ctor_set(v___x_819_, 1, v___f_816_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofName(lean_object* v_n_820_){
_start:
{
uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_821_ = 1;
v___x_822_ = l_Lean_Name_toString(v_n_820_, v___x_821_);
v___x_823_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
v___x_824_ = l_Lean_MessageData_ofFormat(v___x_823_);
return v___x_824_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(lean_object* v_o_828_, lean_object* v_k_829_, uint8_t v_v_830_){
_start:
{
lean_object* v_map_831_; uint8_t v_hasTrace_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_846_; 
v_map_831_ = lean_ctor_get(v_o_828_, 0);
v_hasTrace_832_ = lean_ctor_get_uint8(v_o_828_, sizeof(void*)*1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_o_828_);
if (v_isSharedCheck_846_ == 0)
{
v___x_834_ = v_o_828_;
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_map_831_);
lean_dec(v_o_828_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_836_, 0, v_v_830_);
lean_inc(v_k_829_);
v___x_837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_829_, v___x_836_, v_map_831_);
if (v_hasTrace_832_ == 0)
{
lean_object* v___x_838_; uint8_t v___x_839_; lean_object* v___x_841_; 
v___x_838_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___closed__1));
v___x_839_ = l_Lean_Name_isPrefixOf(v___x_838_, v_k_829_);
lean_dec(v_k_829_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_837_);
v___x_841_ = v___x_834_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_837_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*1, v___x_839_);
return v___x_841_;
}
}
else
{
lean_object* v___x_844_; 
lean_dec(v_k_829_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_837_);
v___x_844_ = v___x_834_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_845_, sizeof(void*)*1, v_hasTrace_832_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_828_ = stack[0].m_obj;
lean_object* v_k_829_ = stack[1].m_obj;
uint8_t v_v_830_ = stack[2].m_num;
lean_object* v_res_847_;
v_res_847_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_828_, v_k_829_, v_v_830_);
stack->m_obj
 = v_res_847_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0___boxed(lean_object* v_o_848_, lean_object* v_k_849_, lean_object* v_v_850_){
_start:
{
uint8_t v_v_boxed_851_; lean_object* v_res_852_; 
v_v_boxed_851_ = lean_unbox(v_v_850_);
v_res_852_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_o_848_, v_k_849_, v_v_boxed_851_);
return v_res_852_;
}
}
lean_object* l_Lean_MessageData_ofConstName___lam__1(lean_object* v___x_858_, lean_object* v_constName_859_, uint8_t v_fullNames_860_, lean_object* v_ctx_x3f_861_){
_start:
{
lean_object* v_val_864_; lean_object* v___y_868_; 
if (lean_obj_tag(v_ctx_x3f_861_) == 0)
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_869_ = 1;
v___x_870_ = l_Lean_Name_toString(v_constName_859_, v___x_869_);
v___x_871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
v___x_872_ = lean_box(1);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v_val_864_ = v___x_873_;
goto v___jp_863_;
}
else
{
if (v_fullNames_860_ == 0)
{
lean_object* v_val_874_; lean_object* v___x_875_; 
v_val_874_ = lean_ctor_get(v_ctx_x3f_861_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v_ctx_x3f_861_, 1);
v___x_875_ = l_Lean_ppConstNameWithInfos(v_val_874_, v_constName_859_);
v___y_868_ = v___x_875_;
goto v___jp_867_;
}
else
{
lean_object* v_val_876_; lean_object* v_env_877_; lean_object* v_mctx_878_; lean_object* v_lctx_879_; lean_object* v_opts_880_; lean_object* v_currNamespace_881_; lean_object* v_openDecls_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_892_; 
v_val_876_ = lean_ctor_get(v_ctx_x3f_861_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v_ctx_x3f_861_, 1);
v_env_877_ = lean_ctor_get(v_val_876_, 0);
v_mctx_878_ = lean_ctor_get(v_val_876_, 1);
v_lctx_879_ = lean_ctor_get(v_val_876_, 2);
v_opts_880_ = lean_ctor_get(v_val_876_, 3);
v_currNamespace_881_ = lean_ctor_get(v_val_876_, 4);
v_openDecls_882_ = lean_ctor_get(v_val_876_, 5);
v_isSharedCheck_892_ = !lean_is_exclusive(v_val_876_);
if (v_isSharedCheck_892_ == 0)
{
v___x_884_ = v_val_876_;
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_openDecls_882_);
lean_inc(v_currNamespace_881_);
lean_inc(v_opts_880_);
lean_inc(v_lctx_879_);
lean_inc(v_mctx_878_);
lean_inc(v_env_877_);
lean_dec(v_val_876_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_892_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = ((lean_object*)(l_Lean_MessageData_ofConstName___lam__1___closed__2));
v___x_887_ = l_Lean_Options_set___at___00Lean_MessageData_ofConstName_spec__0(v_opts_880_, v___x_886_, v_fullNames_860_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 3, v___x_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_env_877_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_mctx_878_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_lctx_879_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_891_, 4, v_currNamespace_881_);
lean_ctor_set(v_reuseFailAlloc_891_, 5, v_openDecls_882_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_ppConstNameWithInfos(v___x_889_, v_constName_859_);
v___y_868_ = v___x_890_;
goto v___jp_867_;
}
}
}
}
v___jp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v_val_864_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_858_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
return v___x_866_;
}
v___jp_867_:
{
v_val_864_ = v___y_868_;
goto v___jp_863_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_ofConstName___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_858_ = stack[0].m_obj;
lean_object* v_constName_859_ = stack[1].m_obj;
uint8_t v_fullNames_860_ = stack[2].m_num;
lean_object* v_ctx_x3f_861_ = stack[3].m_obj;
lean_object* v_res_893_;
v_res_893_ = l_Lean_MessageData_ofConstName___lam__1(v___x_858_, v_constName_859_, v_fullNames_860_, v_ctx_x3f_861_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___lam__1___boxed(lean_object* v___x_894_, lean_object* v_constName_895_, lean_object* v_fullNames_896_, lean_object* v_ctx_x3f_897_, lean_object* v___y_898_){
_start:
{
uint8_t v_fullNames_boxed_899_; lean_object* v_res_900_; 
v_fullNames_boxed_899_ = lean_unbox(v_fullNames_896_);
v_res_900_ = l_Lean_MessageData_ofConstName___lam__1(v___x_894_, v_constName_895_, v_fullNames_boxed_899_, v_ctx_x3f_897_);
return v_res_900_;
}
}
lean_object* l_Lean_MessageData_ofConstName(lean_object* v_constName_901_, uint8_t v_fullNames_902_){
_start:
{
lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; 
v___f_903_ = ((lean_object*)(l_Lean_MessageData_ofSyntax___closed__0));
v___x_904_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_905_ = lean_box(v_fullNames_902_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofConstName___lam__1___boxed), 5, 3);
lean_closure_set(v___f_906_, 0, v___x_904_);
lean_closure_set(v___f_906_, 1, v_constName_901_);
lean_closure_set(v___f_906_, 2, v___x_905_);
v___x_907_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_907_, 0, v___f_906_);
lean_ctor_set(v___x_907_, 1, v___f_903_);
return v___x_907_;
}
}
LEAN_EXPORT void l_Lean_MessageData_ofConstName_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_901_ = stack[0].m_obj;
uint8_t v_fullNames_902_ = stack[1].m_num;
lean_object* v_res_908_;
v_res_908_ = l_Lean_MessageData_ofConstName(v_constName_901_, v_fullNames_902_);
stack->m_obj
 = v_res_908_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConstName___boxed(lean_object* v_constName_909_, lean_object* v_fullNames_910_){
_start:
{
uint8_t v_fullNames_boxed_911_; lean_object* v_res_912_; 
v_fullNames_boxed_911_ = lean_unbox(v_fullNames_910_);
v_res_912_ = l_Lean_MessageData_ofConstName(v_constName_909_, v_fullNames_boxed_911_);
return v_res_912_;
}
}
lean_object* l_Lean_MessageData_withExprHover___lam__0(lean_object* v_val_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v_val_913_);
return v___x_916_;
}
}
LEAN_EXPORT void l_Lean_MessageData_withExprHover___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_913_ = stack[0].m_obj;
lean_object* v___y_914_ = stack[1].m_obj;
lean_object* v_res_917_;
v_res_917_ = l_Lean_MessageData_withExprHover___lam__0(v_val_913_, v___y_914_);
stack->m_obj
 = v_res_917_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___lam__0___boxed(lean_object* v_val_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_MessageData_withExprHover___lam__0(v_val_918_, v___y_919_);
lean_dec_ref(v___y_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(lean_object* v_k_922_, lean_object* v_v_923_, lean_object* v_t_924_){
_start:
{
if (lean_obj_tag(v_t_924_) == 0)
{
lean_object* v_size_925_; lean_object* v_k_926_; lean_object* v_v_927_; lean_object* v_l_928_; lean_object* v_r_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_1210_; 
v_size_925_ = lean_ctor_get(v_t_924_, 0);
v_k_926_ = lean_ctor_get(v_t_924_, 1);
v_v_927_ = lean_ctor_get(v_t_924_, 2);
v_l_928_ = lean_ctor_get(v_t_924_, 3);
v_r_929_ = lean_ctor_get(v_t_924_, 4);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_t_924_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_931_ = v_t_924_;
v_isShared_932_ = v_isSharedCheck_1210_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_r_929_);
lean_inc(v_l_928_);
lean_inc(v_v_927_);
lean_inc(v_k_926_);
lean_inc(v_size_925_);
lean_dec(v_t_924_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_1210_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
uint8_t v___x_933_; 
v___x_933_ = lean_nat_dec_lt(v_k_922_, v_k_926_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; 
v___x_934_ = lean_nat_dec_eq(v_k_922_, v_k_926_);
if (v___x_934_ == 0)
{
lean_object* v_impl_935_; lean_object* v___x_936_; 
lean_dec(v_size_925_);
v_impl_935_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_922_, v_v_923_, v_r_929_);
v___x_936_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_928_) == 0)
{
lean_object* v_size_937_; lean_object* v_size_938_; lean_object* v_k_939_; lean_object* v_v_940_; lean_object* v_l_941_; lean_object* v_r_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_size_937_ = lean_ctor_get(v_l_928_, 0);
v_size_938_ = lean_ctor_get(v_impl_935_, 0);
v_k_939_ = lean_ctor_get(v_impl_935_, 1);
v_v_940_ = lean_ctor_get(v_impl_935_, 2);
v_l_941_ = lean_ctor_get(v_impl_935_, 3);
lean_inc(v_l_941_);
v_r_942_ = lean_ctor_get(v_impl_935_, 4);
v___x_943_ = lean_unsigned_to_nat(3u);
v___x_944_ = lean_nat_mul(v___x_943_, v_size_937_);
v___x_945_ = lean_nat_dec_lt(v___x_944_, v_size_938_);
lean_dec(v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec(v_l_941_);
v___x_946_ = lean_nat_add(v___x_936_, v_size_937_);
v___x_947_ = lean_nat_add(v___x_946_, v_size_938_);
lean_dec(v___x_946_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_impl_935_);
lean_ctor_set(v___x_931_, 0, v___x_947_);
v___x_949_ = v___x_931_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_l_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_impl_935_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_1014_; 
lean_inc(v_r_942_);
lean_inc(v_v_940_);
lean_inc(v_k_939_);
lean_inc(v_size_938_);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_impl_935_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1015_ = lean_ctor_get(v_impl_935_, 4);
lean_dec(v_unused_1015_);
v_unused_1016_ = lean_ctor_get(v_impl_935_, 3);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_impl_935_, 2);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_impl_935_, 1);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_impl_935_, 0);
lean_dec(v_unused_1019_);
v___x_952_ = v_impl_935_;
v_isShared_953_ = v_isSharedCheck_1014_;
goto v_resetjp_951_;
}
else
{
lean_dec(v_impl_935_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_1014_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_size_954_; lean_object* v_k_955_; lean_object* v_v_956_; lean_object* v_l_957_; lean_object* v_r_958_; lean_object* v_size_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_size_954_ = lean_ctor_get(v_l_941_, 0);
v_k_955_ = lean_ctor_get(v_l_941_, 1);
v_v_956_ = lean_ctor_get(v_l_941_, 2);
v_l_957_ = lean_ctor_get(v_l_941_, 3);
v_r_958_ = lean_ctor_get(v_l_941_, 4);
v_size_959_ = lean_ctor_get(v_r_942_, 0);
v___x_960_ = lean_unsigned_to_nat(2u);
v___x_961_ = lean_nat_mul(v___x_960_, v_size_959_);
v___x_962_ = lean_nat_dec_lt(v_size_954_, v___x_961_);
lean_dec(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_990_; 
lean_inc(v_r_958_);
lean_inc(v_l_957_);
lean_inc(v_v_956_);
lean_inc(v_k_955_);
v_isSharedCheck_990_ = !lean_is_exclusive(v_l_941_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; lean_object* v_unused_992_; lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_991_ = lean_ctor_get(v_l_941_, 4);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_941_, 3);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_l_941_, 2);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_l_941_, 1);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_l_941_, 0);
lean_dec(v_unused_995_);
v___x_964_ = v_l_941_;
v_isShared_965_ = v_isSharedCheck_990_;
goto v_resetjp_963_;
}
else
{
lean_dec(v_l_941_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_990_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_980_; 
v___x_966_ = lean_nat_add(v___x_936_, v_size_937_);
v___x_967_ = lean_nat_add(v___x_966_, v_size_938_);
lean_dec(v_size_938_);
if (lean_obj_tag(v_l_957_) == 0)
{
lean_object* v_size_988_; 
v_size_988_ = lean_ctor_get(v_l_957_, 0);
lean_inc(v_size_988_);
v___y_980_ = v_size_988_;
goto v___jp_979_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___y_980_ = v___x_989_;
goto v___jp_979_;
}
v___jp_968_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_nat_add(v___y_969_, v___y_971_);
lean_dec(v___y_971_);
lean_dec(v___y_969_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 4, v_r_942_);
lean_ctor_set(v___x_964_, 3, v_r_958_);
lean_ctor_set(v___x_964_, 2, v_v_940_);
lean_ctor_set(v___x_964_, 1, v_k_939_);
lean_ctor_set(v___x_964_, 0, v___x_972_);
v___x_974_ = v___x_964_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_r_958_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_r_942_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 4, v___x_974_);
lean_ctor_set(v___x_952_, 3, v___y_970_);
lean_ctor_set(v___x_952_, 2, v_v_956_);
lean_ctor_set(v___x_952_, 1, v_k_955_);
lean_ctor_set(v___x_952_, 0, v___x_967_);
v___x_976_ = v___x_952_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_955_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_956_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v___y_970_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_nat_add(v___x_966_, v___y_980_);
lean_dec(v___y_980_);
lean_dec(v___x_966_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_l_957_);
lean_ctor_set(v___x_931_, 0, v___x_981_);
v___x_983_ = v___x_931_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_l_928_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_l_957_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = lean_nat_add(v___x_936_, v_size_959_);
if (lean_obj_tag(v_r_958_) == 0)
{
lean_object* v_size_985_; 
v_size_985_ = lean_ctor_get(v_r_958_, 0);
lean_inc(v_size_985_);
v___y_969_ = v___x_984_;
v___y_970_ = v___x_983_;
v___y_971_ = v_size_985_;
goto v___jp_968_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_unsigned_to_nat(0u);
v___y_969_ = v___x_984_;
v___y_970_ = v___x_983_;
v___y_971_ = v___x_986_;
goto v___jp_968_;
}
}
}
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_del_object(v___x_931_);
v___x_996_ = lean_nat_add(v___x_936_, v_size_937_);
v___x_997_ = lean_nat_add(v___x_996_, v_size_938_);
lean_dec(v_size_938_);
v___x_998_ = lean_nat_add(v___x_996_, v_size_954_);
lean_dec(v___x_996_);
lean_inc_ref(v_l_928_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 4, v_l_941_);
lean_ctor_set(v___x_952_, 3, v_l_928_);
lean_ctor_set(v___x_952_, 2, v_v_927_);
lean_ctor_set(v___x_952_, 1, v_k_926_);
lean_ctor_set(v___x_952_, 0, v___x_998_);
v___x_1000_ = v___x_952_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_l_928_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_l_941_);
v___x_1000_ = v_reuseFailAlloc_1013_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_isSharedCheck_1007_ = !lean_is_exclusive(v_l_928_);
if (v_isSharedCheck_1007_ == 0)
{
lean_object* v_unused_1008_; lean_object* v_unused_1009_; lean_object* v_unused_1010_; lean_object* v_unused_1011_; lean_object* v_unused_1012_; 
v_unused_1008_ = lean_ctor_get(v_l_928_, 4);
lean_dec(v_unused_1008_);
v_unused_1009_ = lean_ctor_get(v_l_928_, 3);
lean_dec(v_unused_1009_);
v_unused_1010_ = lean_ctor_get(v_l_928_, 2);
lean_dec(v_unused_1010_);
v_unused_1011_ = lean_ctor_get(v_l_928_, 1);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_l_928_, 0);
lean_dec(v_unused_1012_);
v___x_1002_ = v_l_928_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v_l_928_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 4, v_r_942_);
lean_ctor_set(v___x_1002_, 3, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v_v_940_);
lean_ctor_set(v___x_1002_, 1, v_k_939_);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_k_939_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_v_940_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1006_, 4, v_r_942_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1020_; 
v_l_1020_ = lean_ctor_get(v_impl_935_, 3);
lean_inc(v_l_1020_);
if (lean_obj_tag(v_l_1020_) == 0)
{
lean_object* v_r_1021_; lean_object* v_k_1022_; lean_object* v_v_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1046_; 
v_r_1021_ = lean_ctor_get(v_impl_935_, 4);
v_k_1022_ = lean_ctor_get(v_impl_935_, 1);
v_v_1023_ = lean_ctor_get(v_impl_935_, 2);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_impl_935_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; lean_object* v_unused_1048_; 
v_unused_1047_ = lean_ctor_get(v_impl_935_, 3);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v_impl_935_, 0);
lean_dec(v_unused_1048_);
v___x_1025_ = v_impl_935_;
v_isShared_1026_ = v_isSharedCheck_1046_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_r_1021_);
lean_inc(v_v_1023_);
lean_inc(v_k_1022_);
lean_dec(v_impl_935_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1046_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_k_1027_; lean_object* v_v_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1042_; 
v_k_1027_ = lean_ctor_get(v_l_1020_, 1);
v_v_1028_ = lean_ctor_get(v_l_1020_, 2);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_l_1020_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v_l_1020_, 4);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v_l_1020_, 3);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v_l_1020_, 0);
lean_dec(v_unused_1045_);
v___x_1030_ = v_l_1020_;
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_v_1028_);
lean_inc(v_k_1027_);
lean_dec(v_l_1020_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1032_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1021_, 2);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 4, v_r_1021_);
lean_ctor_set(v___x_1030_, 3, v_r_1021_);
lean_ctor_set(v___x_1030_, 2, v_v_927_);
lean_ctor_set(v___x_1030_, 1, v_k_926_);
lean_ctor_set(v___x_1030_, 0, v___x_936_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_r_1021_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_r_1021_);
v___x_1034_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1036_; 
lean_inc(v_r_1021_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 3, v_r_1021_);
lean_ctor_set(v___x_1025_, 0, v___x_936_);
v___x_1036_ = v___x_1025_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_k_1022_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_v_1023_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_r_1021_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_r_1021_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_1036_);
lean_ctor_set(v___x_931_, 3, v___x_1034_);
lean_ctor_set(v___x_931_, 2, v_v_1028_);
lean_ctor_set(v___x_931_, 1, v_k_1027_);
lean_ctor_set(v___x_931_, 0, v___x_1032_);
v___x_1038_ = v___x_931_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_k_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_v_1028_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
}
else
{
lean_object* v_r_1049_; 
v_r_1049_ = lean_ctor_get(v_impl_935_, 4);
lean_inc(v_r_1049_);
if (lean_obj_tag(v_r_1049_) == 0)
{
lean_object* v_k_1050_; lean_object* v_v_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1062_; 
v_k_1050_ = lean_ctor_get(v_impl_935_, 1);
v_v_1051_ = lean_ctor_get(v_impl_935_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_impl_935_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; lean_object* v_unused_1064_; lean_object* v_unused_1065_; 
v_unused_1063_ = lean_ctor_get(v_impl_935_, 4);
lean_dec(v_unused_1063_);
v_unused_1064_ = lean_ctor_get(v_impl_935_, 3);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_impl_935_, 0);
lean_dec(v_unused_1065_);
v___x_1053_ = v_impl_935_;
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_v_1051_);
lean_inc(v_k_1050_);
lean_dec(v_impl_935_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1062_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_unsigned_to_nat(3u);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v_l_1020_);
lean_ctor_set(v___x_1053_, 2, v_v_927_);
lean_ctor_set(v___x_1053_, 1, v_k_926_);
lean_ctor_set(v___x_1053_, 0, v___x_936_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v_l_1020_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v_l_1020_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_r_1049_);
lean_ctor_set(v___x_931_, 3, v___x_1057_);
lean_ctor_set(v___x_931_, 2, v_v_1051_);
lean_ctor_set(v___x_931_, 1, v_k_1050_);
lean_ctor_set(v___x_931_, 0, v___x_1055_);
v___x_1059_ = v___x_931_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_k_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_v_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v_r_1049_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(2u);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_impl_935_);
lean_ctor_set(v___x_931_, 3, v_r_1049_);
lean_ctor_set(v___x_931_, 0, v___x_1066_);
v___x_1068_ = v___x_931_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_r_1049_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v_impl_935_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_v_927_);
lean_dec(v_k_926_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 2, v_v_923_);
lean_ctor_set(v___x_931_, 1, v_k_922_);
v___x_1071_ = v___x_931_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_size_925_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_k_922_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_v_923_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_l_928_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_r_929_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
else
{
lean_object* v_impl_1073_; lean_object* v___x_1074_; 
lean_dec(v_size_925_);
v_impl_1073_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_922_, v_v_923_, v_l_928_);
v___x_1074_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_929_) == 0)
{
lean_object* v_size_1075_; lean_object* v_size_1076_; lean_object* v_k_1077_; lean_object* v_v_1078_; lean_object* v_l_1079_; lean_object* v_r_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_size_1075_ = lean_ctor_get(v_r_929_, 0);
v_size_1076_ = lean_ctor_get(v_impl_1073_, 0);
v_k_1077_ = lean_ctor_get(v_impl_1073_, 1);
v_v_1078_ = lean_ctor_get(v_impl_1073_, 2);
v_l_1079_ = lean_ctor_get(v_impl_1073_, 3);
v_r_1080_ = lean_ctor_get(v_impl_1073_, 4);
lean_inc(v_r_1080_);
v___x_1081_ = lean_unsigned_to_nat(3u);
v___x_1082_ = lean_nat_mul(v___x_1081_, v_size_1075_);
v___x_1083_ = lean_nat_dec_lt(v___x_1082_, v_size_1076_);
lean_dec(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec(v_r_1080_);
v___x_1084_ = lean_nat_add(v___x_1074_, v_size_1076_);
v___x_1085_ = lean_nat_add(v___x_1084_, v_size_1075_);
lean_dec(v___x_1084_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 3, v_impl_1073_);
lean_ctor_set(v___x_931_, 0, v___x_1085_);
v___x_1087_ = v___x_931_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_impl_1073_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_r_929_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
else
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_l_1079_);
lean_inc(v_v_1078_);
lean_inc(v_k_1077_);
lean_inc(v_size_1076_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_impl_1073_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1155_ = lean_ctor_get(v_impl_1073_, 4);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_impl_1073_, 3);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_impl_1073_, 2);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_impl_1073_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v_impl_1073_, 0);
lean_dec(v_unused_1159_);
v___x_1090_ = v_impl_1073_;
v_isShared_1091_ = v_isSharedCheck_1154_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_impl_1073_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1154_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_size_1092_; lean_object* v_size_1093_; lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v_l_1096_; lean_object* v_r_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_size_1092_ = lean_ctor_get(v_l_1079_, 0);
v_size_1093_ = lean_ctor_get(v_r_1080_, 0);
v_k_1094_ = lean_ctor_get(v_r_1080_, 1);
v_v_1095_ = lean_ctor_get(v_r_1080_, 2);
v_l_1096_ = lean_ctor_get(v_r_1080_, 3);
v_r_1097_ = lean_ctor_get(v_r_1080_, 4);
v___x_1098_ = lean_unsigned_to_nat(2u);
v___x_1099_ = lean_nat_mul(v___x_1098_, v_size_1092_);
v___x_1100_ = lean_nat_dec_lt(v_size_1093_, v___x_1099_);
lean_dec(v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1129_; 
lean_inc(v_r_1097_);
lean_inc(v_l_1096_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_r_1080_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; lean_object* v_unused_1131_; lean_object* v_unused_1132_; lean_object* v_unused_1133_; lean_object* v_unused_1134_; 
v_unused_1130_ = lean_ctor_get(v_r_1080_, 4);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_r_1080_, 3);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_r_1080_, 2);
lean_dec(v_unused_1132_);
v_unused_1133_ = lean_ctor_get(v_r_1080_, 1);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_r_1080_, 0);
lean_dec(v_unused_1134_);
v___x_1102_ = v_r_1080_;
v_isShared_1103_ = v_isSharedCheck_1129_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_r_1080_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1129_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___x_1117_; lean_object* v___y_1119_; 
v___x_1104_ = lean_nat_add(v___x_1074_, v_size_1076_);
lean_dec(v_size_1076_);
v___x_1105_ = lean_nat_add(v___x_1104_, v_size_1075_);
lean_dec(v___x_1104_);
v___x_1117_ = lean_nat_add(v___x_1074_, v_size_1092_);
if (lean_obj_tag(v_l_1096_) == 0)
{
lean_object* v_size_1127_; 
v_size_1127_ = lean_ctor_get(v_l_1096_, 0);
lean_inc(v_size_1127_);
v___y_1119_ = v_size_1127_;
goto v___jp_1118_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___y_1119_ = v___x_1128_;
goto v___jp_1118_;
}
v___jp_1106_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_nat_add(v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec(v___y_1108_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 4, v_r_929_);
lean_ctor_set(v___x_1102_, 3, v_r_1097_);
lean_ctor_set(v___x_1102_, 2, v_v_927_);
lean_ctor_set(v___x_1102_, 1, v_k_926_);
lean_ctor_set(v___x_1102_, 0, v___x_1110_);
v___x_1112_ = v___x_1102_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_r_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_r_929_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v___x_1112_);
lean_ctor_set(v___x_1090_, 3, v___y_1107_);
lean_ctor_set(v___x_1090_, 2, v_v_1095_);
lean_ctor_set(v___x_1090_, 1, v_k_1094_);
lean_ctor_set(v___x_1090_, 0, v___x_1105_);
v___x_1114_ = v___x_1090_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_k_1094_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_v_1095_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v___y_1107_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
v___jp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = lean_nat_add(v___x_1117_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec(v___x_1117_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_l_1096_);
lean_ctor_set(v___x_931_, 3, v_l_1079_);
lean_ctor_set(v___x_931_, 2, v_v_1078_);
lean_ctor_set(v___x_931_, 1, v_k_1077_);
lean_ctor_set(v___x_931_, 0, v___x_1120_);
v___x_1122_ = v___x_931_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1077_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1078_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_l_1079_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_l_1096_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_nat_add(v___x_1074_, v_size_1075_);
if (lean_obj_tag(v_r_1097_) == 0)
{
lean_object* v_size_1124_; 
v_size_1124_ = lean_ctor_get(v_r_1097_, 0);
lean_inc(v_size_1124_);
v___y_1107_ = v___x_1122_;
v___y_1108_ = v___x_1123_;
v___y_1109_ = v_size_1124_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___y_1107_ = v___x_1122_;
v___y_1108_ = v___x_1123_;
v___y_1109_ = v___x_1125_;
goto v___jp_1106_;
}
}
}
}
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
lean_del_object(v___x_931_);
v___x_1135_ = lean_nat_add(v___x_1074_, v_size_1076_);
lean_dec(v_size_1076_);
v___x_1136_ = lean_nat_add(v___x_1135_, v_size_1075_);
lean_dec(v___x_1135_);
v___x_1137_ = lean_nat_add(v___x_1074_, v_size_1075_);
v___x_1138_ = lean_nat_add(v___x_1137_, v_size_1093_);
lean_dec(v___x_1137_);
lean_inc_ref(v_r_929_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 4, v_r_929_);
lean_ctor_set(v___x_1090_, 3, v_r_1080_);
lean_ctor_set(v___x_1090_, 2, v_v_927_);
lean_ctor_set(v___x_1090_, 1, v_k_926_);
lean_ctor_set(v___x_1090_, 0, v___x_1138_);
v___x_1140_ = v___x_1090_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_r_1080_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_r_929_);
v___x_1140_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v_r_929_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1148_ = lean_ctor_get(v_r_929_, 4);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_r_929_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_r_929_, 2);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_929_, 1);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_r_929_, 0);
lean_dec(v_unused_1152_);
v___x_1142_ = v_r_929_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_dec(v_r_929_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 4, v___x_1140_);
lean_ctor_set(v___x_1142_, 3, v_l_1079_);
lean_ctor_set(v___x_1142_, 2, v_v_1078_);
lean_ctor_set(v___x_1142_, 1, v_k_1077_);
lean_ctor_set(v___x_1142_, 0, v___x_1136_);
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_k_1077_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_v_1078_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_l_1079_);
lean_ctor_set(v_reuseFailAlloc_1146_, 4, v___x_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1160_; 
v_l_1160_ = lean_ctor_get(v_impl_1073_, 3);
if (lean_obj_tag(v_l_1160_) == 0)
{
lean_object* v_r_1161_; lean_object* v_k_1162_; lean_object* v_v_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1174_; 
lean_inc_ref(v_l_1160_);
v_r_1161_ = lean_ctor_get(v_impl_1073_, 4);
v_k_1162_ = lean_ctor_get(v_impl_1073_, 1);
v_v_1163_ = lean_ctor_get(v_impl_1073_, 2);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_impl_1073_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1175_ = lean_ctor_get(v_impl_1073_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_impl_1073_, 0);
lean_dec(v_unused_1176_);
v___x_1165_ = v_impl_1073_;
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_r_1161_);
lean_inc(v_v_1163_);
lean_inc(v_k_1162_);
lean_dec(v_impl_1073_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1174_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1161_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 3, v_r_1161_);
lean_ctor_set(v___x_1165_, 2, v_v_927_);
lean_ctor_set(v___x_1165_, 1, v_k_926_);
lean_ctor_set(v___x_1165_, 0, v___x_1074_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_r_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_r_1161_);
v___x_1169_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1171_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_1169_);
lean_ctor_set(v___x_931_, 3, v_l_1160_);
lean_ctor_set(v___x_931_, 2, v_v_1163_);
lean_ctor_set(v___x_931_, 1, v_k_1162_);
lean_ctor_set(v___x_931_, 0, v___x_1167_);
v___x_1171_ = v___x_931_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1162_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1163_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_l_1160_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_r_1177_; 
v_r_1177_ = lean_ctor_get(v_impl_1073_, 4);
lean_inc(v_r_1177_);
if (lean_obj_tag(v_r_1177_) == 0)
{
lean_object* v_k_1178_; lean_object* v_v_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1202_; 
lean_inc(v_l_1160_);
v_k_1178_ = lean_ctor_get(v_impl_1073_, 1);
v_v_1179_ = lean_ctor_get(v_impl_1073_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_impl_1073_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; 
v_unused_1203_ = lean_ctor_get(v_impl_1073_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_impl_1073_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_impl_1073_, 0);
lean_dec(v_unused_1205_);
v___x_1181_ = v_impl_1073_;
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_v_1179_);
lean_inc(v_k_1178_);
lean_dec(v_impl_1073_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1202_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_k_1183_; lean_object* v_v_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1198_; 
v_k_1183_ = lean_ctor_get(v_r_1177_, 1);
v_v_1184_ = lean_ctor_get(v_r_1177_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_r_1177_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1199_ = lean_ctor_get(v_r_1177_, 4);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_r_1177_, 3);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1177_, 0);
lean_dec(v_unused_1201_);
v___x_1186_ = v_r_1177_;
v_isShared_1187_ = v_isSharedCheck_1198_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_v_1184_);
lean_inc(v_k_1183_);
lean_dec(v_r_1177_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1198_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(3u);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 4, v_l_1160_);
lean_ctor_set(v___x_1186_, 3, v_l_1160_);
lean_ctor_set(v___x_1186_, 2, v_v_1179_);
lean_ctor_set(v___x_1186_, 1, v_k_1178_);
lean_ctor_set(v___x_1186_, 0, v___x_1074_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_k_1178_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_v_1179_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_l_1160_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_l_1160_);
v___x_1190_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 4, v_l_1160_);
lean_ctor_set(v___x_1181_, 2, v_v_927_);
lean_ctor_set(v___x_1181_, 1, v_k_926_);
lean_ctor_set(v___x_1181_, 0, v___x_1074_);
v___x_1192_ = v___x_1181_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_l_1160_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_l_1160_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1194_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_1192_);
lean_ctor_set(v___x_931_, 3, v___x_1190_);
lean_ctor_set(v___x_931_, 2, v_v_1184_);
lean_ctor_set(v___x_931_, 1, v_k_1183_);
lean_ctor_set(v___x_931_, 0, v___x_1188_);
v___x_1194_ = v___x_931_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1183_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1184_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_unsigned_to_nat(2u);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v_r_1177_);
lean_ctor_set(v___x_931_, 3, v_impl_1073_);
lean_ctor_set(v___x_931_, 0, v___x_1206_);
v___x_1208_ = v___x_931_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_926_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_927_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_impl_1073_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1177_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v_k_922_);
lean_ctor_set(v___x_1212_, 2, v_v_923_);
lean_ctor_set(v___x_1212_, 3, v_t_924_);
lean_ctor_set(v___x_1212_, 4, v_t_924_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(lean_object* v_as_x27_1213_, lean_object* v_b_1214_){
_start:
{
if (lean_obj_tag(v_as_x27_1213_) == 0)
{
return v_b_1214_;
}
else
{
lean_object* v_head_1215_; lean_object* v_tail_1216_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v_r_1219_; 
v_head_1215_ = lean_ctor_get(v_as_x27_1213_, 0);
v_tail_1216_ = lean_ctor_get(v_as_x27_1213_, 1);
v_fst_1217_ = lean_ctor_get(v_head_1215_, 0);
v_snd_1218_ = lean_ctor_get(v_head_1215_, 1);
lean_inc(v_snd_1218_);
lean_inc(v_fst_1217_);
v_r_1219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_fst_1217_, v_snd_1218_, v_b_1214_);
v_as_x27_1213_ = v_tail_1216_;
v_b_1214_ = v_r_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg___boxed(lean_object* v_as_x27_1221_, lean_object* v_b_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1221_, v_b_1222_);
lean_dec(v_as_x27_1221_);
return v_res_1223_;
}
}
lean_object* l_Lean_MessageData_withExprHover(lean_object* v_fmt_1232_, lean_object* v_expr_1233_, lean_object* v_lctx_1234_, lean_object* v_location_x3f_1235_, lean_object* v_docString_x3f_1236_, lean_object* v_mkDocString_x3f_1237_, uint8_t v_explicit_1238_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___y_1246_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v_fmt_1232_);
v___x_1241_ = ((lean_object*)(l_Lean_MessageData_withExprHover___closed__3));
v___x_1242_ = lean_box(0);
v___x_1243_ = 0;
v___x_1244_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1244_, 0, v___x_1241_);
lean_ctor_set(v___x_1244_, 1, v_lctx_1234_);
lean_ctor_set(v___x_1244_, 2, v___x_1242_);
lean_ctor_set(v___x_1244_, 3, v_expr_1233_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*4, v___x_1243_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*4 + 1, v___x_1243_);
if (lean_obj_tag(v_mkDocString_x3f_1237_) == 0)
{
if (lean_obj_tag(v_docString_x3f_1236_) == 0)
{
v___y_1246_ = v_mkDocString_x3f_1237_;
goto v___jp_1245_;
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
v_val_1256_ = lean_ctor_get(v_docString_x3f_1236_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_docString_x3f_1236_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1258_ = v_docString_x3f_1236_;
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_val_1256_);
lean_dec(v_docString_x3f_1236_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___f_1260_; lean_object* v___x_1262_; 
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHover___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1260_, 0, v_val_1256_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___f_1260_);
v___x_1262_ = v___x_1258_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___f_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
v___y_1246_ = v___x_1262_;
goto v___jp_1245_;
}
}
}
}
else
{
lean_dec(v_docString_x3f_1236_);
v___y_1246_ = v_mkDocString_x3f_1237_;
goto v___jp_1245_;
}
v___jp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_r_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1247_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v_location_x3f_1235_);
lean_ctor_set(v___x_1247_, 2, v___y_1246_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*3, v_explicit_1238_);
v___x_1248_ = lean_alloc_ctor(13, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1239_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v_r_1252_ = lean_box(1);
v___x_1253_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v___x_1251_, v_r_1252_);
lean_dec_ref_known(v___x_1251_, 2);
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1240_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
return v___x_1255_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_withExprHover_0interp(lean_interpreter_value* stack)
{
lean_object* v_fmt_1232_ = stack[0].m_obj;
lean_object* v_expr_1233_ = stack[1].m_obj;
lean_object* v_lctx_1234_ = stack[2].m_obj;
lean_object* v_location_x3f_1235_ = stack[3].m_obj;
lean_object* v_docString_x3f_1236_ = stack[4].m_obj;
lean_object* v_mkDocString_x3f_1237_ = stack[5].m_obj;
uint8_t v_explicit_1238_ = stack[6].m_num;
lean_object* v_res_1265_;
v_res_1265_ = l_Lean_MessageData_withExprHover(v_fmt_1232_, v_expr_1233_, v_lctx_1234_, v_location_x3f_1235_, v_docString_x3f_1236_, v_mkDocString_x3f_1237_, v_explicit_1238_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHover___boxed(lean_object* v_fmt_1266_, lean_object* v_expr_1267_, lean_object* v_lctx_1268_, lean_object* v_location_x3f_1269_, lean_object* v_docString_x3f_1270_, lean_object* v_mkDocString_x3f_1271_, lean_object* v_explicit_1272_){
_start:
{
uint8_t v_explicit_boxed_1273_; lean_object* v_res_1274_; 
v_explicit_boxed_1273_ = lean_unbox(v_explicit_1272_);
v_res_1274_ = l_Lean_MessageData_withExprHover(v_fmt_1266_, v_expr_1267_, v_lctx_1268_, v_location_x3f_1269_, v_docString_x3f_1270_, v_mkDocString_x3f_1271_, v_explicit_boxed_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0(lean_object* v_00_u03b2_1275_, lean_object* v_k_1276_, lean_object* v_v_1277_, lean_object* v_t_1278_, lean_object* v_hl_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_MessageData_withExprHover_spec__0___redArg(v_k_1276_, v_v_1277_, v_t_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(lean_object* v_as_1281_, lean_object* v_as_x27_1282_, lean_object* v_b_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___redArg(v_as_x27_1282_, v_b_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1___boxed(lean_object* v_as_1286_, lean_object* v_as_x27_1287_, lean_object* v_b_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_List_forIn_x27_loop___at___00Lean_MessageData_withExprHover_spec__1(v_as_1286_, v_as_x27_1287_, v_b_1288_, v_a_1289_);
lean_dec(v_as_x27_1287_);
lean_dec(v_as_1286_);
return v_res_1290_;
}
}
lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0(lean_object* v_fmt_1291_, lean_object* v_expr_1292_, lean_object* v_location_x3f_1293_, lean_object* v_docString_x3f_1294_, lean_object* v_mkDocString_x3f_1295_, uint8_t v_explicit_1296_, lean_object* v_toPure_1297_, lean_object* v_lctx_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = l_Lean_MessageData_withExprHover(v_fmt_1291_, v_expr_1292_, v_lctx_1298_, v_location_x3f_1293_, v_docString_x3f_1294_, v_mkDocString_x3f_1295_, v_explicit_1296_);
v___x_1300_ = lean_apply_2(v_toPure_1297_, lean_box(0), v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT void l_Lean_MessageData_withExprHoverM___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fmt_1291_ = stack[0].m_obj;
lean_object* v_expr_1292_ = stack[1].m_obj;
lean_object* v_location_x3f_1293_ = stack[2].m_obj;
lean_object* v_docString_x3f_1294_ = stack[3].m_obj;
lean_object* v_mkDocString_x3f_1295_ = stack[4].m_obj;
uint8_t v_explicit_1296_ = stack[5].m_num;
lean_object* v_toPure_1297_ = stack[6].m_obj;
lean_object* v_lctx_1298_ = stack[7].m_obj;
lean_object* v_res_1301_;
v_res_1301_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1291_, v_expr_1292_, v_location_x3f_1293_, v_docString_x3f_1294_, v_mkDocString_x3f_1295_, v_explicit_1296_, v_toPure_1297_, v_lctx_1298_);
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed(lean_object* v_fmt_1302_, lean_object* v_expr_1303_, lean_object* v_location_x3f_1304_, lean_object* v_docString_x3f_1305_, lean_object* v_mkDocString_x3f_1306_, lean_object* v_explicit_1307_, lean_object* v_toPure_1308_, lean_object* v_lctx_1309_){
_start:
{
uint8_t v_explicit_boxed_1310_; lean_object* v_res_1311_; 
v_explicit_boxed_1310_ = lean_unbox(v_explicit_1307_);
v_res_1311_ = l_Lean_MessageData_withExprHoverM___redArg___lam__0(v_fmt_1302_, v_expr_1303_, v_location_x3f_1304_, v_docString_x3f_1305_, v_mkDocString_x3f_1306_, v_explicit_boxed_1310_, v_toPure_1308_, v_lctx_1309_);
return v_res_1311_;
}
}
lean_object* l_Lean_MessageData_withExprHoverM___redArg(lean_object* v_inst_1312_, lean_object* v_inst_1313_, lean_object* v_fmt_1314_, lean_object* v_expr_1315_, lean_object* v_lctx_x3f_1316_, lean_object* v_location_x3f_1317_, lean_object* v_docString_x3f_1318_, lean_object* v_mkDocString_x3f_1319_, uint8_t v_explicit_1320_){
_start:
{
lean_object* v_toApplicative_1321_; lean_object* v_toBind_1322_; lean_object* v_toPure_1323_; lean_object* v___x_1324_; lean_object* v___f_1325_; 
v_toApplicative_1321_ = lean_ctor_get(v_inst_1312_, 0);
lean_inc_ref(v_toApplicative_1321_);
v_toBind_1322_ = lean_ctor_get(v_inst_1312_, 1);
lean_inc(v_toBind_1322_);
lean_dec_ref(v_inst_1312_);
v_toPure_1323_ = lean_ctor_get(v_toApplicative_1321_, 1);
lean_inc_n(v_toPure_1323_, 2);
lean_dec_ref(v_toApplicative_1321_);
v___x_1324_ = lean_box(v_explicit_1320_);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_MessageData_withExprHoverM___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1325_, 0, v_fmt_1314_);
lean_closure_set(v___f_1325_, 1, v_expr_1315_);
lean_closure_set(v___f_1325_, 2, v_location_x3f_1317_);
lean_closure_set(v___f_1325_, 3, v_docString_x3f_1318_);
lean_closure_set(v___f_1325_, 4, v_mkDocString_x3f_1319_);
lean_closure_set(v___f_1325_, 5, v___x_1324_);
lean_closure_set(v___f_1325_, 6, v_toPure_1323_);
if (lean_obj_tag(v_lctx_x3f_1316_) == 0)
{
lean_object* v___x_1326_; 
lean_dec(v_toPure_1323_);
v___x_1326_ = lean_apply_4(v_toBind_1322_, lean_box(0), lean_box(0), v_inst_1313_, v___f_1325_);
return v___x_1326_;
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_inst_1313_);
v_val_1327_ = lean_ctor_get(v_lctx_x3f_1316_, 0);
lean_inc(v_val_1327_);
lean_dec_ref_known(v_lctx_x3f_1316_, 1);
v___x_1328_ = lean_apply_2(v_toPure_1323_, lean_box(0), v_val_1327_);
v___x_1329_ = lean_apply_4(v_toBind_1322_, lean_box(0), lean_box(0), v___x_1328_, v___f_1325_);
return v___x_1329_;
}
}
}
LEAN_EXPORT void l_Lean_MessageData_withExprHoverM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1312_ = stack[0].m_obj;
lean_object* v_inst_1313_ = stack[1].m_obj;
lean_object* v_fmt_1314_ = stack[2].m_obj;
lean_object* v_expr_1315_ = stack[3].m_obj;
lean_object* v_lctx_x3f_1316_ = stack[4].m_obj;
lean_object* v_location_x3f_1317_ = stack[5].m_obj;
lean_object* v_docString_x3f_1318_ = stack[6].m_obj;
lean_object* v_mkDocString_x3f_1319_ = stack[7].m_obj;
uint8_t v_explicit_1320_ = stack[8].m_num;
lean_object* v_res_1330_;
v_res_1330_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1312_, v_inst_1313_, v_fmt_1314_, v_expr_1315_, v_lctx_x3f_1316_, v_location_x3f_1317_, v_docString_x3f_1318_, v_mkDocString_x3f_1319_, v_explicit_1320_);
stack->m_obj
 = v_res_1330_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___redArg___boxed(lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_fmt_1333_, lean_object* v_expr_1334_, lean_object* v_lctx_x3f_1335_, lean_object* v_location_x3f_1336_, lean_object* v_docString_x3f_1337_, lean_object* v_mkDocString_x3f_1338_, lean_object* v_explicit_1339_){
_start:
{
uint8_t v_explicit_boxed_1340_; lean_object* v_res_1341_; 
v_explicit_boxed_1340_ = lean_unbox(v_explicit_1339_);
v_res_1341_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1331_, v_inst_1332_, v_fmt_1333_, v_expr_1334_, v_lctx_x3f_1335_, v_location_x3f_1336_, v_docString_x3f_1337_, v_mkDocString_x3f_1338_, v_explicit_boxed_1340_);
return v_res_1341_;
}
}
lean_object* l_Lean_MessageData_withExprHoverM(lean_object* v_m_1342_, lean_object* v_inst_1343_, lean_object* v_inst_1344_, lean_object* v_fmt_1345_, lean_object* v_expr_1346_, lean_object* v_lctx_x3f_1347_, lean_object* v_location_x3f_1348_, lean_object* v_docString_x3f_1349_, lean_object* v_mkDocString_x3f_1350_, uint8_t v_explicit_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1343_, v_inst_1344_, v_fmt_1345_, v_expr_1346_, v_lctx_x3f_1347_, v_location_x3f_1348_, v_docString_x3f_1349_, v_mkDocString_x3f_1350_, v_explicit_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT void l_Lean_MessageData_withExprHoverM_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1343_ = stack[1].m_obj;
lean_object* v_inst_1344_ = stack[2].m_obj;
lean_object* v_fmt_1345_ = stack[3].m_obj;
lean_object* v_expr_1346_ = stack[4].m_obj;
lean_object* v_lctx_x3f_1347_ = stack[5].m_obj;
lean_object* v_location_x3f_1348_ = stack[6].m_obj;
lean_object* v_docString_x3f_1349_ = stack[7].m_obj;
lean_object* v_mkDocString_x3f_1350_ = stack[8].m_obj;
uint8_t v_explicit_1351_ = stack[9].m_num;
lean_object* v_res_1353_;
v_res_1353_ = l_Lean_MessageData_withExprHoverM(lean_box(0), v_inst_1343_, v_inst_1344_, v_fmt_1345_, v_expr_1346_, v_lctx_x3f_1347_, v_location_x3f_1348_, v_docString_x3f_1349_, v_mkDocString_x3f_1350_, v_explicit_1351_);
stack->m_obj
 = v_res_1353_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_withExprHoverM___boxed(lean_object* v_m_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_fmt_1357_, lean_object* v_expr_1358_, lean_object* v_lctx_x3f_1359_, lean_object* v_location_x3f_1360_, lean_object* v_docString_x3f_1361_, lean_object* v_mkDocString_x3f_1362_, lean_object* v_explicit_1363_){
_start:
{
uint8_t v_explicit_boxed_1364_; lean_object* v_res_1365_; 
v_explicit_boxed_1364_ = lean_unbox(v_explicit_1363_);
v_res_1365_ = l_Lean_MessageData_withExprHoverM(v_m_1354_, v_inst_1355_, v_inst_1356_, v_fmt_1357_, v_expr_1358_, v_lctx_x3f_1359_, v_location_x3f_1360_, v_docString_x3f_1361_, v_mkDocString_x3f_1362_, v_explicit_boxed_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0(lean_object* v_userName_1366_, lean_object* v_display_1367_, lean_object* v_toPure_1368_, lean_object* v_inst_1369_, lean_object* v_inst_1370_, lean_object* v_____do__lift_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_LocalContext_findFromUserName_x3f(v_____do__lift_1371_, v_userName_1366_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_dec(v_inst_1370_);
lean_dec_ref(v_inst_1369_);
v___x_1373_ = l_Lean_MessageData_ofName(v_display_1367_);
v___x_1374_ = lean_apply_2(v_toPure_1368_, lean_box(0), v___x_1373_);
return v___x_1374_;
}
else
{
lean_object* v_val_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v_toPure_1368_);
v_val_1375_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1377_ = v___x_1372_;
v_isShared_1378_ = v_isSharedCheck_1389_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_val_1375_);
lean_dec(v___x_1372_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1389_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
uint8_t v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1379_ = 1;
v___x_1380_ = l_Lean_Name_toString(v_display_1367_, v___x_1379_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 3);
lean_ctor_set(v___x_1377_, 0, v___x_1380_);
v___x_1382_ = v___x_1377_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1383_ = l_Lean_LocalDecl_fvarId(v_val_1375_);
lean_dec(v_val_1375_);
v___x_1384_ = l_Lean_Expr_fvar___override(v___x_1383_);
v___x_1385_ = lean_box(0);
v___x_1386_ = 0;
v___x_1387_ = l_Lean_MessageData_withExprHoverM___redArg(v_inst_1369_, v_inst_1370_, v___x_1382_, v___x_1384_, v___x_1385_, v___x_1385_, v___x_1385_, v___x_1385_, v___x_1386_);
return v___x_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg___lam__0___boxed(lean_object* v_userName_1390_, lean_object* v_display_1391_, lean_object* v_toPure_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_____do__lift_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_MessageData_ofUserName___redArg___lam__0(v_userName_1390_, v_display_1391_, v_toPure_1392_, v_inst_1393_, v_inst_1394_, v_____do__lift_1395_);
lean_dec_ref(v_____do__lift_1395_);
lean_dec(v_userName_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName___redArg(lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_userName_1399_){
_start:
{
lean_object* v_toApplicative_1400_; lean_object* v_toBind_1401_; lean_object* v_toPure_1402_; lean_object* v_display_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v_toApplicative_1400_ = lean_ctor_get(v_inst_1397_, 0);
v_toBind_1401_ = lean_ctor_get(v_inst_1397_, 1);
lean_inc(v_toBind_1401_);
v_toPure_1402_ = lean_ctor_get(v_toApplicative_1400_, 1);
lean_inc(v_toPure_1402_);
lean_inc(v_userName_1399_);
v_display_1403_ = l_Lean_Name_simpMacroScopes(v_userName_1399_);
lean_inc(v_inst_1398_);
v___f_1404_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofUserName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1404_, 0, v_userName_1399_);
lean_closure_set(v___f_1404_, 1, v_display_1403_);
lean_closure_set(v___f_1404_, 2, v_toPure_1402_);
lean_closure_set(v___f_1404_, 3, v_inst_1397_);
lean_closure_set(v___f_1404_, 4, v_inst_1398_);
v___x_1405_ = lean_apply_4(v_toBind_1401_, lean_box(0), lean_box(0), v_inst_1398_, v___f_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofUserName(lean_object* v_m_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_userName_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_MessageData_ofUserName___redArg(v_inst_1407_, v_inst_1408_, v_userName_1409_);
return v___x_1410_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1415_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set(v___x_1417_, 1, v___x_1416_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
lean_ctor_set(v___x_1417_, 3, v___x_1416_);
lean_ctor_set(v___x_1417_, 4, v___x_1415_);
lean_ctor_set(v___x_1417_, 5, v___x_1415_);
lean_ctor_set(v___x_1417_, 6, v___x_1415_);
lean_ctor_set(v___x_1417_, 7, v___x_1415_);
lean_ctor_set(v___x_1417_, 8, v___x_1415_);
lean_ctor_set(v___x_1417_, 9, v___x_1415_);
lean_ctor_set(v___x_1417_, 10, v___x_1415_);
lean_ctor_set(v___x_1417_, 11, v___x_1414_);
return v___x_1417_;
}
}
uint8_t l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(lean_object* v_mctx_x3f_1418_, lean_object* v_a_1419_){
_start:
{
switch(lean_obj_tag(v_a_1419_))
{
case 10:
{
if (lean_obj_tag(v_mctx_x3f_1418_) == 0)
{
lean_object* v_hasSyntheticSorry_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v_hasSyntheticSorry_1420_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_hasSyntheticSorry_1420_);
lean_dec_ref_known(v_a_1419_, 2);
v___x_1421_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_1422_ = lean_apply_1(v_hasSyntheticSorry_1420_, v___x_1421_);
v___x_1423_ = lean_unbox(v___x_1422_);
return v___x_1423_;
}
else
{
lean_object* v_hasSyntheticSorry_1424_; lean_object* v_val_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_hasSyntheticSorry_1424_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_hasSyntheticSorry_1424_);
lean_dec_ref_known(v_a_1419_, 2);
v_val_1425_ = lean_ctor_get(v_mctx_x3f_1418_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v_mctx_x3f_1418_, 1);
v___x_1426_ = lean_apply_1(v_hasSyntheticSorry_1424_, v_val_1425_);
v___x_1427_ = lean_unbox(v___x_1426_);
return v___x_1427_;
}
}
case 3:
{
lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v_mctx_1430_; lean_object* v___x_1431_; 
lean_dec(v_mctx_x3f_1418_);
v_a_1428_ = lean_ctor_get(v_a_1419_, 0);
lean_inc_ref(v_a_1428_);
v_a_1429_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1429_);
lean_dec_ref_known(v_a_1419_, 2);
v_mctx_1430_ = lean_ctor_get(v_a_1428_, 1);
lean_inc_ref(v_mctx_1430_);
lean_dec_ref(v_a_1428_);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_mctx_1430_);
v_mctx_x3f_1418_ = v___x_1431_;
v_a_1419_ = v_a_1429_;
goto _start;
}
case 4:
{
lean_object* v_a_1433_; 
v_a_1433_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1433_);
lean_dec_ref_known(v_a_1419_, 2);
v_a_1419_ = v_a_1433_;
goto _start;
}
case 5:
{
lean_object* v_a_1435_; 
v_a_1435_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1435_);
lean_dec_ref_known(v_a_1419_, 2);
v_a_1419_ = v_a_1435_;
goto _start;
}
case 6:
{
lean_object* v_a_1437_; 
v_a_1437_ = lean_ctor_get(v_a_1419_, 0);
lean_inc_ref(v_a_1437_);
lean_dec_ref_known(v_a_1419_, 1);
v_a_1419_ = v_a_1437_;
goto _start;
}
case 7:
{
lean_object* v_a_1439_; lean_object* v_a_1440_; uint8_t v___x_1441_; 
v_a_1439_ = lean_ctor_get(v_a_1419_, 0);
lean_inc_ref(v_a_1439_);
v_a_1440_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1440_);
lean_dec_ref_known(v_a_1419_, 2);
lean_inc(v_mctx_x3f_1418_);
v___x_1441_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1418_, v_a_1439_);
if (v___x_1441_ == 0)
{
v_a_1419_ = v_a_1440_;
goto _start;
}
else
{
lean_dec_ref(v_a_1440_);
lean_dec(v_mctx_x3f_1418_);
return v___x_1441_;
}
}
case 8:
{
lean_object* v_a_1443_; 
v_a_1443_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1443_);
lean_dec_ref_known(v_a_1419_, 2);
v_a_1419_ = v_a_1443_;
goto _start;
}
case 11:
{
lean_object* v_a_1445_; 
v_a_1445_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_a_1445_);
lean_dec_ref_known(v_a_1419_, 2);
v_a_1419_ = v_a_1445_;
goto _start;
}
case 9:
{
lean_object* v_msg_1447_; lean_object* v_children_1448_; uint8_t v___x_1449_; 
v_msg_1447_ = lean_ctor_get(v_a_1419_, 1);
lean_inc_ref(v_msg_1447_);
v_children_1448_ = lean_ctor_get(v_a_1419_, 2);
lean_inc_ref(v_children_1448_);
lean_dec_ref_known(v_a_1419_, 3);
lean_inc(v_mctx_x3f_1418_);
v___x_1449_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1418_, v_msg_1447_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = lean_array_get_size(v_children_1448_);
v___x_1452_ = lean_nat_dec_lt(v___x_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_dec_ref(v_children_1448_);
lean_dec(v_mctx_x3f_1418_);
return v___x_1452_;
}
else
{
if (v___x_1452_ == 0)
{
lean_dec_ref(v_children_1448_);
lean_dec(v_mctx_x3f_1418_);
return v___x_1452_;
}
else
{
size_t v___x_1453_; size_t v___x_1454_; uint8_t v___x_1455_; 
v___x_1453_ = ((size_t)0ULL);
v___x_1454_ = lean_usize_of_nat(v___x_1451_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1418_, v_children_1448_, v___x_1453_, v___x_1454_);
lean_dec_ref(v_children_1448_);
return v___x_1455_;
}
}
}
else
{
lean_dec_ref(v_children_1448_);
lean_dec(v_mctx_x3f_1418_);
return v___x_1449_;
}
}
default: 
{
uint8_t v___x_1456_; 
lean_dec_ref(v_a_1419_);
lean_dec(v_mctx_x3f_1418_);
v___x_1456_ = 0;
return v___x_1456_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_x3f_1418_ = stack[0].m_obj;
lean_object* v_a_1419_ = stack[1].m_obj;
uint8_t v_res_1457_;
v_res_1457_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1418_, v_a_1419_);
stack->m_num = v_res_1457_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(lean_object* v_mctx_x3f_1458_, lean_object* v_as_1459_, size_t v_i_1460_, size_t v_stop_1461_){
_start:
{
uint8_t v___x_1462_; 
v___x_1462_ = lean_usize_dec_eq(v_i_1460_, v_stop_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = lean_array_uget_borrowed(v_as_1459_, v_i_1460_);
lean_inc(v___x_1463_);
lean_inc(v_mctx_x3f_1458_);
v___x_1464_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1458_, v___x_1463_);
if (v___x_1464_ == 0)
{
size_t v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = ((size_t)1ULL);
v___x_1466_ = lean_usize_add(v_i_1460_, v___x_1465_);
v_i_1460_ = v___x_1466_;
goto _start;
}
else
{
lean_dec(v_mctx_x3f_1458_);
return v___x_1464_;
}
}
else
{
uint8_t v___x_1468_; 
lean_dec(v_mctx_x3f_1458_);
v___x_1468_ = 0;
return v___x_1468_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_x3f_1458_ = stack[0].m_obj;
lean_object* v_as_1459_ = stack[1].m_obj;
size_t v_i_1460_ = stack[2].m_num;
size_t v_stop_1461_ = stack[3].m_num;
uint8_t v_res_1469_;
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1458_, v_as_1459_, v_i_1460_, v_stop_1461_);
stack->m_num = v_res_1469_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0___boxed(lean_object* v_mctx_x3f_1470_, lean_object* v_as_1471_, lean_object* v_i_1472_, lean_object* v_stop_1473_){
_start:
{
size_t v_i_boxed_1474_; size_t v_stop_boxed_1475_; uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_i_boxed_1474_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_stop_boxed_1475_ = lean_unbox_usize(v_stop_1473_);
lean_dec(v_stop_1473_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit_spec__0(v_mctx_x3f_1470_, v_as_1471_, v_i_boxed_1474_, v_stop_boxed_1475_);
lean_dec_ref(v_as_1471_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* v_mctx_x3f_1478_, lean_object* v_a_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v_mctx_x3f_1478_, v_a_1479_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* v_msg_1482_){
_start:
{
lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1483_ = lean_box(0);
v___x_1484_ = l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit(v___x_1483_, v_msg_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT void l_Lean_MessageData_hasSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1482_ = stack[0].m_obj;
uint8_t v_res_1485_;
v_res_1485_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1482_);
stack->m_num = v_res_1485_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* v_msg_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Lean_MessageData_hasSyntheticSorry(v_msg_1486_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(lean_object* v_name_1489_, lean_object* v_decl_1490_, lean_object* v_ref_1491_){
_start:
{
lean_object* v_defValue_1493_; lean_object* v_descr_1494_; lean_object* v_deprecation_x3f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_defValue_1493_ = lean_ctor_get(v_decl_1490_, 0);
v_descr_1494_ = lean_ctor_get(v_decl_1490_, 1);
v_deprecation_x3f_1495_ = lean_ctor_get(v_decl_1490_, 2);
lean_inc(v_defValue_1493_);
v___x_1496_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1496_, 0, v_defValue_1493_);
lean_inc(v_deprecation_x3f_1495_);
lean_inc_ref(v_descr_1494_);
lean_inc_n(v_name_1489_, 2);
v___x_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1497_, 0, v_name_1489_);
lean_ctor_set(v___x_1497_, 1, v_ref_1491_);
lean_ctor_set(v___x_1497_, 2, v___x_1496_);
lean_ctor_set(v___x_1497_, 3, v_descr_1494_);
lean_ctor_set(v___x_1497_, 4, v_deprecation_x3f_1495_);
v___x_1498_ = lean_register_option(v_name_1489_, v___x_1497_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1506_; 
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v___x_1498_, 0);
lean_dec(v_unused_1507_);
v___x_1500_ = v___x_1498_;
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v___x_1498_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1506_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_inc(v_defValue_1493_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_name_1489_);
lean_ctor_set(v___x_1502_, 1, v_defValue_1493_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_name_1489_);
v_a_1508_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1498_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1498_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1489_ = stack[0].m_obj;
lean_object* v_decl_1490_ = stack[1].m_obj;
lean_object* v_ref_1491_ = stack[2].m_obj;
lean_object* v_res_1516_;
v_res_1516_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1489_, v_decl_1490_, v_ref_1491_);
stack->m_obj
 = v_res_1516_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1517_, lean_object* v_decl_1518_, lean_object* v_ref_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v_name_1517_, v_decl_1518_, v_ref_1519_);
lean_dec_ref(v_decl_1518_);
return v_res_1521_;
}
}
lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1535_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__1_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1536_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__3_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1537_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_initFn___closed__4_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_));
v___x_1538_ = l_Lean_Option_register___at___00__private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__spec__0(v___x_1535_, v___x_1536_, v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT void l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1539_;
v_res_1539_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
stack->m_obj
 = v_res_1539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4____boxed(lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Message_0__Lean_MessageData_initFn_00___x40_Lean_Message_1828196597____hygCtx___hyg_4_();
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_MessageData_formatAux_spec__0(lean_object* v_a_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_nat_to_int(v_a_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = lean_box(0);
v___x_1545_ = l_instMonadBaseIO;
v___x_1546_ = l_instInhabitedOfMonad___redArg(v___x_1545_, v___x_1544_);
return v___x_1546_;
}
}
lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3(lean_object* v_msg_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1578__overap_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1578__overap_1550_ = lean_panic_fn_borrowed(v___x_1549_, v_msg_1547_);
v___x_1551_ = lean_apply_1(v___x_1578__overap_1550_, lean_box(0));
return v___x_1551_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_MessageData_formatAux_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1547_ = stack[0].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1547_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_MessageData_formatAux_spec__3___boxed(lean_object* v_msg_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v_msg_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_dec(v_x_1556_);
return v_x_1557_;
}
else
{
lean_object* v_head_1559_; lean_object* v_tail_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1569_; 
v_head_1559_ = lean_ctor_get(v_x_1558_, 0);
v_tail_1560_ = lean_ctor_get(v_x_1558_, 1);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1562_ = v_x_1558_;
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_tail_1560_);
lean_inc(v_head_1559_);
lean_dec(v_x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1569_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
lean_inc(v_x_1556_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 5);
lean_ctor_set(v___x_1562_, 1, v_x_1556_);
lean_ctor_set(v___x_1562_, 0, v_x_1557_);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_x_1557_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_x_1556_);
v___x_1565_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_head_1559_);
v_x_1557_ = v___x_1566_;
v_x_1558_ = v_tail_1560_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(lean_object* v_x_1570_, lean_object* v_x_1571_){
_start:
{
if (lean_obj_tag(v_x_1570_) == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_x_1571_);
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
else
{
lean_object* v_tail_1573_; 
v_tail_1573_ = lean_ctor_get(v_x_1570_, 1);
if (lean_obj_tag(v_tail_1573_) == 0)
{
lean_object* v_head_1574_; 
lean_dec(v_x_1571_);
v_head_1574_ = lean_ctor_get(v_x_1570_, 0);
lean_inc(v_head_1574_);
lean_dec_ref_known(v_x_1570_, 2);
return v_head_1574_;
}
else
{
lean_object* v_head_1575_; lean_object* v___x_1576_; 
lean_inc(v_tail_1573_);
v_head_1575_ = lean_ctor_get(v_x_1570_, 0);
lean_inc(v_head_1575_);
lean_dec_ref_known(v_x_1570_, 2);
v___x_1576_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2_spec__2(v_x_1571_, v_head_1575_, v_tail_1573_);
return v___x_1576_;
}
}
}
}
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1591_; double v___x_1592_; 
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_float_of_nat(v___x_1591_);
return v___x_1592_;
}
}
lean_object* l_Lean_MessageData_formatAux(lean_object* v_x_1596_, lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
switch(lean_obj_tag(v_x_1598_))
{
case 0:
{
lean_object* v_a_1600_; lean_object* v_fmt_1601_; 
lean_dec(v_x_1597_);
lean_dec_ref(v_x_1596_);
v_a_1600_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_a_1600_);
lean_dec_ref_known(v_x_1598_, 1);
v_fmt_1601_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_fmt_1601_);
lean_dec_ref(v_a_1600_);
return v_fmt_1601_;
}
case 1:
{
if (lean_obj_tag(v_x_1597_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; 
lean_dec_ref(v_x_1596_);
v_a_1602_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v_x_1598_, 1);
v___x_1603_ = l_Lean_formatRawGoal(v_a_1602_);
return v___x_1603_;
}
else
{
lean_object* v_a_1604_; lean_object* v_val_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_a_1604_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v_x_1598_, 1);
v_val_1605_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_x_1597_, 1);
v___x_1606_ = l_Lean_MessageData_mkPPContext(v_x_1596_, v_val_1605_);
lean_dec(v_val_1605_);
lean_dec_ref(v_x_1596_);
v___x_1607_ = l_Lean_ppGoal(v___x_1606_, v_a_1604_);
return v___x_1607_;
}
}
case 3:
{
lean_object* v_a_1608_; lean_object* v_a_1609_; lean_object* v___x_1610_; 
lean_dec(v_x_1597_);
v_a_1608_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_a_1608_);
v_a_1609_ = lean_ctor_get(v_x_1598_, 1);
lean_inc_ref(v_a_1609_);
lean_dec_ref_known(v_x_1598_, 2);
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_a_1608_);
v_x_1597_ = v___x_1610_;
v_x_1598_ = v_a_1609_;
goto _start;
}
case 4:
{
lean_object* v_a_1612_; lean_object* v_a_1613_; 
lean_dec_ref(v_x_1596_);
v_a_1612_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_a_1612_);
v_a_1613_ = lean_ctor_get(v_x_1598_, 1);
lean_inc_ref(v_a_1613_);
lean_dec_ref_known(v_x_1598_, 2);
v_x_1596_ = v_a_1612_;
v_x_1598_ = v_a_1613_;
goto _start;
}
case 5:
{
lean_object* v_a_1615_; lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
v_a_1615_ = lean_ctor_get(v_x_1598_, 0);
v_a_1616_ = lean_ctor_get(v_x_1598_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1618_ = v_x_1598_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_inc(v_a_1615_);
lean_dec(v_x_1598_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_a_1616_);
v___x_1621_ = lean_nat_to_int(v_a_1615_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 4);
lean_ctor_set(v___x_1618_, 1, v___x_1620_);
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1620_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
case 6:
{
lean_object* v_a_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v_a_1626_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_a_1626_);
lean_dec_ref_known(v_x_1598_, 1);
v___x_1627_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_a_1626_);
v___x_1628_ = 0;
v___x_1629_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*1, v___x_1628_);
return v___x_1629_;
}
case 7:
{
lean_object* v_a_1630_; lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1640_; 
v_a_1630_ = lean_ctor_get(v_x_1598_, 0);
v_a_1631_ = lean_ctor_get(v_x_1598_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1633_ = v_x_1598_;
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_inc(v_a_1630_);
lean_dec(v_x_1598_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
lean_inc(v_x_1597_);
lean_inc_ref(v_x_1596_);
v___x_1635_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_a_1630_);
v___x_1636_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 5);
lean_ctor_set(v___x_1633_, 1, v___x_1636_);
lean_ctor_set(v___x_1633_, 0, v___x_1635_);
v___x_1638_ = v___x_1633_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
case 9:
{
lean_object* v_data_1641_; lean_object* v_msg_1642_; lean_object* v_children_1643_; size_t v_sz_1644_; size_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v_cls_1660_; lean_object* v_result_x3f_1661_; double v_startTime_1662_; double v_stopTime_1663_; lean_object* v_msg_1665_; uint8_t v___x_1680_; 
v_data_1641_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_data_1641_);
v_msg_1642_ = lean_ctor_get(v_x_1598_, 1);
lean_inc_ref(v_msg_1642_);
v_children_1643_ = lean_ctor_get(v_x_1598_, 2);
lean_inc_ref(v_children_1643_);
lean_dec_ref_known(v_x_1598_, 3);
v_sz_1644_ = lean_array_size(v_children_1643_);
v___x_1645_ = ((size_t)0ULL);
lean_inc(v_x_1597_);
lean_inc_ref(v_x_1596_);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1596_, v_x_1597_, v_sz_1644_, v___x_1645_, v_children_1643_);
v_cls_1660_ = lean_ctor_get(v_data_1641_, 0);
lean_inc(v_cls_1660_);
v_result_x3f_1661_ = lean_ctor_get(v_data_1641_, 1);
lean_inc(v_result_x3f_1661_);
v_startTime_1662_ = lean_ctor_get_float(v_data_1641_, sizeof(void*)*3);
v_stopTime_1663_ = lean_ctor_get_float(v_data_1641_, sizeof(void*)*3 + 8);
lean_dec_ref(v_data_1641_);
v___x_1680_ = l_Lean_Name_isAnonymous(v_cls_1660_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; double v___x_1696_; uint8_t v___x_1697_; 
v___x_1681_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__4));
v___x_1682_ = 1;
v___x_1683_ = l_Lean_Name_toString(v_cls_1660_, v___x_1682_);
v___x_1684_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1681_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1687_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1696_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1697_ = lean_float_beq(v_startTime_1662_, v___x_1696_);
if (v___x_1697_ == 0)
{
goto v___jp_1688_;
}
else
{
if (v___x_1680_ == 0)
{
v_msg_1665_ = v___x_1687_;
goto v___jp_1664_;
}
else
{
goto v___jp_1688_;
}
}
v___jp_1688_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; double v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1689_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1687_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_float_sub(v_stopTime_1663_, v_startTime_1662_);
v___x_1692_ = lean_float_to_string(v___x_1691_);
v___x_1693_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1690_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1686_);
v_msg_1665_ = v___x_1695_;
goto v___jp_1664_;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
lean_dec(v_result_x3f_1661_);
lean_dec(v_cls_1660_);
lean_dec_ref(v_msg_1642_);
lean_dec(v_x_1597_);
lean_dec_ref(v_x_1596_);
v___x_1698_ = lean_array_to_list(v___x_1646_);
v___x_1699_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1700_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1698_, v___x_1699_);
return v___x_1700_;
}
v___jp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1650_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l_Lean_instReprTraceResult_repr___closed__6, &l_Lean_instReprTraceResult_repr___closed__6_once, _init_l_Lean_instReprTraceResult_repr___closed__6);
v___x_1653_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1652_);
lean_ctor_set(v___x_1653_, 1, v___y_1649_);
v___x_1654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1651_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_array_to_list(v___x_1646_);
v___x_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1658_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1656_, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1652_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
return v___x_1659_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_msg_1642_);
if (lean_obj_tag(v_result_x3f_1661_) == 0)
{
v___y_1648_ = v_msg_1665_;
v___y_1649_ = v___x_1666_;
goto v___jp_1647_;
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1679_; 
v_val_1667_ = lean_ctor_get(v_result_x3f_1661_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v_result_x3f_1661_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1669_ = v_result_x3f_1661_;
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v_result_x3f_1661_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1679_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1671_ = lean_unbox(v_val_1667_);
lean_dec(v_val_1667_);
v___x_1672_ = l_Lean_TraceResult_toEmoji(v___x_1671_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 3);
lean_ctor_set(v___x_1669_, 0, v___x_1672_);
v___x_1674_ = v___x_1669_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__0));
v___x_1676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1666_);
v___y_1648_ = v_msg_1665_;
v___y_1649_ = v___x_1677_;
goto v___jp_1647_;
}
}
}
}
}
case 10:
{
lean_object* v_f_1701_; lean_object* v___x_1702_; lean_object* v___y_1704_; 
v_f_1701_ = lean_ctor_get(v_x_1598_, 0);
lean_inc_ref(v_f_1701_);
lean_dec_ref_known(v_x_1598_, 2);
v___x_1702_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1597_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_box(0);
v___y_1704_ = v___x_1720_;
goto v___jp_1703_;
}
else
{
lean_object* v_val_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_val_1721_ = lean_ctor_get(v_x_1597_, 0);
v___x_1722_ = l_Lean_MessageData_mkPPContext(v_x_1596_, v_val_1721_);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
v___y_1704_ = v___x_1723_;
goto v___jp_1703_;
}
v___jp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_apply_2(v_f_1701_, v___y_1704_, lean_box(0));
v___x_1706_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1705_, v___x_1702_);
if (lean_obj_tag(v___x_1706_) == 1)
{
lean_object* v_val_1707_; 
lean_dec(v___x_1705_);
v_val_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v___x_1706_, 1);
v_x_1598_ = v_val_1707_;
goto _start;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v___x_1706_);
lean_dec(v_x_1597_);
lean_dec_ref(v_x_1596_);
v___x_1709_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1710_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1711_ = lean_unsigned_to_nat(409u);
v___x_1712_ = lean_unsigned_to_nat(8u);
v___x_1713_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1714_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1705_);
lean_dec(v___x_1705_);
v___x_1715_ = 1;
v___x_1716_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1714_, v___x_1715_);
v___x_1717_ = lean_string_append(v___x_1713_, v___x_1716_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = l_mkPanicMessageWithDecl(v___x_1709_, v___x_1710_, v___x_1711_, v___x_1712_, v___x_1717_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1718_);
return v___x_1719_;
}
}
}
default: 
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v_x_1598_, 1);
lean_inc_ref(v_a_1724_);
lean_dec_ref(v_x_1598_);
v_x_1598_ = v_a_1724_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Lean_MessageData_formatAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1596_ = stack[0].m_obj;
lean_object* v_x_1597_ = stack[1].m_obj;
lean_object* v_x_1598_ = stack[2].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l_Lean_MessageData_formatAux(v_x_1596_, v_x_1597_, v_x_1598_);
stack->m_obj
 = v_res_1726_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1727_, lean_object* v_x_1728_, size_t v_sz_1729_, size_t v_i_1730_, lean_object* v_bs_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
if (v___x_1733_ == 0)
{
lean_dec(v_x_1728_);
lean_dec_ref(v_x_1727_);
return v_bs_1731_;
}
else
{
lean_object* v_v_1734_; lean_object* v___x_1735_; lean_object* v_bs_x27_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; 
v_v_1734_ = lean_array_uget(v_bs_1731_, v_i_1730_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v_bs_x27_1736_ = lean_array_uset(v_bs_1731_, v_i_1730_, v___x_1735_);
lean_inc(v_x_1728_);
lean_inc_ref(v_x_1727_);
v___x_1737_ = l_Lean_MessageData_formatAux(v_x_1727_, v_x_1728_, v_v_1734_);
v___x_1738_ = ((size_t)1ULL);
v___x_1739_ = lean_usize_add(v_i_1730_, v___x_1738_);
v___x_1740_ = lean_array_uset(v_bs_x27_1736_, v_i_1730_, v___x_1737_);
v_i_1730_ = v___x_1739_;
v_bs_1731_ = v___x_1740_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1727_ = stack[0].m_obj;
lean_object* v_x_1728_ = stack[1].m_obj;
size_t v_sz_1729_ = stack[2].m_num;
size_t v_i_1730_ = stack[3].m_num;
lean_object* v_bs_1731_ = stack[4].m_obj;
lean_object* v_res_1742_;
v_res_1742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1727_, v_x_1728_, v_sz_1729_, v_i_1730_, v_bs_1731_);
stack->m_obj
 = v_res_1742_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v_sz_1745_, lean_object* v_i_1746_, lean_object* v_bs_1747_, lean_object* v___y_1748_){
_start:
{
size_t v_sz_boxed_1749_; size_t v_i_boxed_1750_; lean_object* v_res_1751_; 
v_sz_boxed_1749_ = lean_unbox_usize(v_sz_1745_);
lean_dec(v_sz_1745_);
v_i_boxed_1750_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1743_, v_x_1744_, v_sz_boxed_1749_, v_i_boxed_1750_, v_bs_1747_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_MessageData_formatAux(v_x_1752_, v_x_1753_, v_x_1754_);
return v_res_1756_;
}
}
lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1760_, lean_object* v_ctx_x3f_1761_){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1764_ = l_Lean_MessageData_formatAux(v___x_1763_, v_ctx_x3f_1761_, v_msgData_1760_);
return v___x_1764_;
}
}
LEAN_EXPORT void l_Lean_MessageData_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1760_ = stack[0].m_obj;
lean_object* v_ctx_x3f_1761_ = stack[1].m_obj;
lean_object* v_res_1765_;
v_res_1765_ = l_Lean_MessageData_format(v_msgData_1760_, v_ctx_x3f_1761_);
stack->m_obj
 = v_res_1765_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1766_, lean_object* v_ctx_x3f_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_MessageData_format(v_msgData_1766_, v_ctx_x3f_1767_);
return v_res_1769_;
}
}
lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1770_){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = l_Lean_MessageData_format(v_msgData_1770_, v___x_1772_);
v___x_1774_ = l_Std_Format_defWidth;
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = l_Std_Format_pretty(v___x_1773_, v___x_1774_, v___x_1775_, v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT void l_Lean_MessageData_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1770_ = stack[0].m_obj;
lean_object* v_res_1777_;
v_res_1777_ = l_Lean_MessageData_toString(v_msgData_1770_);
stack->m_obj
 = v_res_1777_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_MessageData_toString(v_msgData_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1781_);
lean_ctor_set(v___x_1783_, 1, v_a_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_s_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1812_){
_start:
{
if (lean_obj_tag(v_o_1812_) == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1813_;
}
else
{
lean_object* v_val_1814_; lean_object* v___x_1815_; 
v_val_1814_ = lean_ctor_get(v_o_1812_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v_o_1812_, 1);
v___x_1815_ = l_Lean_MessageData_ofExpr(v_val_1814_);
return v___x_1815_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1819_ = l_Lean_MessageData_ofFormat(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1824_ = l_Lean_MessageData_ofFormat(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1825_, lean_object* v_i_1826_, lean_object* v_acc_1827_){
_start:
{
lean_object* v___y_1829_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v_es_1825_);
v___x_1834_ = lean_nat_dec_lt(v_i_1826_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec(v_i_1826_);
v___x_1835_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1836_, 0, v_acc_1827_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
return v___x_1836_;
}
else
{
lean_object* v_e_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_e_1837_ = lean_array_fget_borrowed(v_es_1825_, v_i_1826_);
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_nat_dec_eq(v_i_1826_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_acc_1827_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
lean_inc(v_e_1837_);
v___x_1842_ = l_Lean_MessageData_ofExpr(v_e_1837_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___y_1829_ = v___x_1843_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_inc(v_e_1837_);
v___x_1844_ = l_Lean_MessageData_ofExpr(v_e_1837_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_acc_1827_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___y_1829_ = v___x_1845_;
goto v___jp_1828_;
}
}
v___jp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_nat_add(v_i_1826_, v___x_1830_);
lean_dec(v_i_1826_);
v_i_1826_ = v___x_1831_;
v_acc_1827_ = v___y_1829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1846_, lean_object* v_i_1847_, lean_object* v_acc_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1846_, v_i_1847_, v_acc_1848_);
lean_dec_ref(v_es_1846_);
return v_res_1849_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1854_ = l_Lean_MessageData_ofFormat(v___x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1858_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1855_, v___x_1856_, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1859_);
lean_dec_ref(v_es_1859_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1863_, lean_object* v_f_1864_, lean_object* v_r_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1866_ = lean_string_length(v_l_1863_);
v___x_1867_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_l_1863_);
v___x_1868_ = l_Lean_MessageData_ofFormat(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v_f_1864_);
v___x_1870_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_r_1865_);
v___x_1871_ = l_Lean_MessageData_ofFormat(v___x_1870_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1869_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1866_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1877_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1878_ = l_Lean_MessageData_bracket(v___x_1876_, v_f_1875_, v___x_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1881_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1882_ = l_Lean_MessageData_bracket(v___x_1880_, v_f_1879_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref(v_x_1884_);
v___x_1885_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1885_;
}
else
{
lean_object* v_tail_1886_; 
v_tail_1886_ = lean_ctor_get(v_x_1883_, 1);
if (lean_obj_tag(v_tail_1886_) == 0)
{
lean_object* v_head_1887_; 
lean_dec_ref(v_x_1884_);
v_head_1887_ = lean_ctor_get(v_x_1883_, 0);
lean_inc(v_head_1887_);
lean_dec_ref_known(v_x_1883_, 2);
return v_head_1887_;
}
else
{
lean_object* v_head_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1897_; 
lean_inc(v_tail_1886_);
v_head_1888_ = lean_ctor_get(v_x_1883_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_x_1883_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_x_1883_, 1);
lean_dec(v_unused_1898_);
v___x_1890_ = v_x_1883_;
v_isShared_1891_ = v_isSharedCheck_1897_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_head_1888_);
lean_dec(v_x_1883_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1897_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
lean_inc_ref(v_x_1884_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 7);
lean_ctor_set(v___x_1890_, 1, v_x_1884_);
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_head_1888_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_x_1884_);
v___x_1893_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = l_Lean_MessageData_joinSep(v_tail_1886_, v_x_1884_);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
return v___x_1895_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1903_ = l_Lean_MessageData_ofFormat(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1908_ = l_Lean_MessageData_ofFormat(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_box(1);
v___x_1910_ = l_Lean_MessageData_ofFormat(v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1912_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v___x_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1914_){
_start:
{
if (lean_obj_tag(v_x_1914_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1915_;
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1917_ = l_Lean_MessageData_joinSep(v_x_1914_, v___x_1916_);
v___x_1918_ = l_Lean_MessageData_sbracket(v___x_1917_);
return v___x_1918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_array_to_list(v_msgs_1919_);
v___x_1921_ = l_Lean_MessageData_ofList(v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1925_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1926_ = l_Lean_MessageData_ofFormat(v___x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1931_ = l_Lean_MessageData_ofFormat(v___x_1930_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1936_ = l_Lean_MessageData_ofFormat(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1937_){
_start:
{
if (lean_obj_tag(v_xs_1937_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1938_;
}
else
{
lean_object* v_tail_1939_; 
v_tail_1939_ = lean_ctor_get(v_xs_1937_, 1);
lean_inc(v_tail_1939_);
if (lean_obj_tag(v_tail_1939_) == 0)
{
lean_object* v_head_1940_; 
v_head_1940_ = lean_ctor_get(v_xs_1937_, 0);
lean_inc(v_head_1940_);
lean_dec_ref_known(v_xs_1937_, 2);
return v_head_1940_;
}
else
{
lean_object* v_tail_1941_; 
v_tail_1941_ = lean_ctor_get(v_tail_1939_, 1);
if (lean_obj_tag(v_tail_1941_) == 0)
{
lean_object* v_head_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1959_; 
v_head_1942_ = lean_ctor_get(v_xs_1937_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_xs_1937_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v_xs_1937_, 1);
lean_dec(v_unused_1960_);
v___x_1944_ = v_xs_1937_;
v_isShared_1945_ = v_isSharedCheck_1959_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_head_1942_);
lean_dec(v_xs_1937_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1959_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v_head_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1957_; 
v_head_1946_ = lean_ctor_get(v_tail_1939_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_tail_1939_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v_tail_1939_, 1);
lean_dec(v_unused_1958_);
v___x_1948_ = v_tail_1939_;
v_isShared_1949_ = v_isSharedCheck_1957_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_head_1946_);
lean_dec(v_tail_1939_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1957_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 7);
lean_ctor_set(v___x_1948_, 1, v___x_1950_);
lean_ctor_set(v___x_1948_, 0, v_head_1942_);
v___x_1952_ = v___x_1948_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_head_1942_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1950_);
v___x_1952_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set_tag(v___x_1944_, 7);
lean_ctor_set(v___x_1944_, 1, v_head_1946_);
lean_ctor_set(v___x_1944_, 0, v___x_1952_);
v___x_1954_ = v___x_1944_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_head_1946_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1984_; 
v_isSharedCheck_1984_ = !lean_is_exclusive(v_tail_1939_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1985_ = lean_ctor_get(v_tail_1939_, 1);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_tail_1939_, 0);
lean_dec(v_unused_1986_);
v___x_1962_ = v_tail_1939_;
v_isShared_1963_ = v_isSharedCheck_1984_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v_tail_1939_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1984_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1964_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1937_);
v___x_1965_ = lean_array_mk(v_xs_1937_);
v___x_1966_ = lean_array_pop(v___x_1965_);
v___x_1967_ = lean_array_to_list(v___x_1966_);
v___x_1968_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1969_ = l_Lean_MessageData_joinSep(v___x_1967_, v___x_1968_);
v___x_1970_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1963_ == 0)
{
lean_ctor_set_tag(v___x_1962_, 7);
lean_ctor_set(v___x_1962_, 1, v___x_1970_);
lean_ctor_set(v___x_1962_, 0, v___x_1969_);
v___x_1972_ = v___x_1962_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v___x_1973_ = l_List_getLast_x21___redArg(v___x_1964_, v_xs_1937_);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_xs_1937_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; lean_object* v_unused_1982_; 
v_unused_1981_ = lean_ctor_get(v_xs_1937_, 1);
lean_dec(v_unused_1981_);
v_unused_1982_ = lean_ctor_get(v_xs_1937_, 0);
lean_dec(v_unused_1982_);
v___x_1975_ = v_xs_1937_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_dec(v_xs_1937_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set_tag(v___x_1975_, 7);
lean_ctor_set(v___x_1975_, 1, v___x_1973_);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
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
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1991_ = l_Lean_MessageData_ofFormat(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1996_ = l_Lean_MessageData_ofFormat(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1997_){
_start:
{
if (lean_obj_tag(v_xs_1997_) == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1998_;
}
else
{
lean_object* v_tail_1999_; 
v_tail_1999_ = lean_ctor_get(v_xs_1997_, 1);
lean_inc(v_tail_1999_);
if (lean_obj_tag(v_tail_1999_) == 0)
{
lean_object* v_head_2000_; 
v_head_2000_ = lean_ctor_get(v_xs_1997_, 0);
lean_inc(v_head_2000_);
lean_dec_ref_known(v_xs_1997_, 2);
return v_head_2000_;
}
else
{
lean_object* v_tail_2001_; 
v_tail_2001_ = lean_ctor_get(v_tail_1999_, 1);
if (lean_obj_tag(v_tail_2001_) == 0)
{
lean_object* v_head_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2019_; 
v_head_2002_ = lean_ctor_get(v_xs_1997_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_xs_1997_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v_xs_1997_, 1);
lean_dec(v_unused_2020_);
v___x_2004_ = v_xs_1997_;
v_isShared_2005_ = v_isSharedCheck_2019_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_head_2002_);
lean_dec(v_xs_1997_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2019_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_head_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2017_; 
v_head_2006_ = lean_ctor_get(v_tail_1999_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_tail_1999_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_tail_1999_, 1);
lean_dec(v_unused_2018_);
v___x_2008_ = v_tail_1999_;
v_isShared_2009_ = v_isSharedCheck_2017_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_head_2006_);
lean_dec(v_tail_1999_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2017_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
v___x_2010_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_2009_ == 0)
{
lean_ctor_set_tag(v___x_2008_, 7);
lean_ctor_set(v___x_2008_, 1, v___x_2010_);
lean_ctor_set(v___x_2008_, 0, v_head_2002_);
v___x_2012_ = v___x_2008_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_head_2002_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2014_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 7);
lean_ctor_set(v___x_2004_, 1, v_head_2006_);
lean_ctor_set(v___x_2004_, 0, v___x_2012_);
v___x_2014_ = v___x_2004_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_head_2006_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2044_; 
v_isSharedCheck_2044_ = !lean_is_exclusive(v_tail_1999_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2045_ = lean_ctor_get(v_tail_1999_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_tail_1999_, 0);
lean_dec(v_unused_2046_);
v___x_2022_ = v_tail_1999_;
v_isShared_2023_ = v_isSharedCheck_2044_;
goto v_resetjp_2021_;
}
else
{
lean_dec(v_tail_1999_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2044_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2024_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1997_);
v___x_2025_ = lean_array_mk(v_xs_1997_);
v___x_2026_ = lean_array_pop(v___x_2025_);
v___x_2027_ = lean_array_to_list(v___x_2026_);
v___x_2028_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_2029_ = l_Lean_MessageData_joinSep(v___x_2027_, v___x_2028_);
v___x_2030_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 7);
lean_ctor_set(v___x_2022_, 1, v___x_2030_);
lean_ctor_set(v___x_2022_, 0, v___x_2029_);
v___x_2032_ = v___x_2022_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v___x_2033_ = l_List_getLast_x21___redArg(v___x_2024_, v_xs_1997_);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_xs_1997_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; lean_object* v_unused_2042_; 
v_unused_2041_ = lean_ctor_get(v_xs_1997_, 1);
lean_dec(v_unused_2041_);
v_unused_2042_ = lean_ctor_get(v_xs_1997_, 0);
lean_dec(v_unused_2042_);
v___x_2035_ = v_xs_1997_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v_xs_1997_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 7);
lean_ctor_set(v___x_2035_, 1, v___x_2033_);
lean_ctor_set(v___x_2035_, 0, v___x_2032_);
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
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
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2053_ = l_Lean_MessageData_ofFormat(v___x_2052_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2055_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2054_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_note_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2064_ = l_Lean_MessageData_ofFormat(v___x_2063_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2066_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___x_2065_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v_hint_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2073_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2074_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2075_ = lean_box(0);
v___x_2076_ = l_List_mapTR_loop___redArg(v___x_2074_, v_es_2073_, v___x_2075_);
v___x_2077_ = l_Lean_MessageData_ofList(v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2081_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2082_ = l_Lean_instInhabitedPosition_default;
v___x_2083_ = lean_box(0);
v___x_2084_ = 0;
v___x_2085_ = 2;
v___x_2086_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2086_, 0, v___x_2081_);
lean_ctor_set(v___x_2086_, 1, v___x_2082_);
lean_ctor_set(v___x_2086_, 2, v___x_2083_);
lean_ctor_set(v___x_2086_, 3, v___x_2081_);
lean_ctor_set(v___x_2086_, 4, v_inst_2080_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*5, v___x_2084_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*5 + 1, v___x_2085_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*5 + 2, v___x_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2087_, lean_object* v_inst_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2092_, lean_object* v_inst_2093_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_fileName_2109_; lean_object* v_pos_2110_; lean_object* v_endPos_2111_; uint8_t v_keepFullRange_2112_; uint8_t v_severity_2113_; uint8_t v_isSilent_2114_; lean_object* v_caption_2115_; lean_object* v_data_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_fileName_2109_ = lean_ctor_get(v_x_2108_, 0);
lean_inc_ref(v_fileName_2109_);
v_pos_2110_ = lean_ctor_get(v_x_2108_, 1);
lean_inc_ref(v_pos_2110_);
v_endPos_2111_ = lean_ctor_get(v_x_2108_, 2);
lean_inc(v_endPos_2111_);
v_keepFullRange_2112_ = lean_ctor_get_uint8(v_x_2108_, sizeof(void*)*5);
v_severity_2113_ = lean_ctor_get_uint8(v_x_2108_, sizeof(void*)*5 + 1);
v_isSilent_2114_ = lean_ctor_get_uint8(v_x_2108_, sizeof(void*)*5 + 2);
v_caption_2115_ = lean_ctor_get(v_x_2108_, 3);
lean_inc_ref(v_caption_2115_);
v_data_2116_ = lean_ctor_get(v_x_2108_, 4);
lean_inc(v_data_2116_);
lean_dec_ref(v_x_2108_);
v___x_2117_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2118_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2119_, 0, v_fileName_2109_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2124_ = l_Lean_instToJsonPosition_toJson(v_pos_2110_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___x_2121_);
v___x_2127_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2128_ = l_Lean_Option_toJson___redArg(v___x_2117_, v_endPos_2111_);
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2121_);
v___x_2131_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2132_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2132_, 0, v_keepFullRange_2112_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2121_);
v___x_2135_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2136_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2113_);
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_2121_);
v___x_2139_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2140_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2140_, 0, v_isSilent_2114_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2139_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2121_);
v___x_2143_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_caption_2115_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v___x_2121_);
v___x_2147_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2148_ = lean_apply_1(v_inst_2107_, v_data_2116_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
lean_ctor_set(v___x_2150_, 1, v___x_2121_);
v___x_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
lean_ctor_set(v___x_2151_, 1, v___x_2121_);
v___x_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2146_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2142_);
lean_ctor_set(v___x_2153_, 1, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2138_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2134_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2130_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2126_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2122_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2160_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2161_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2159_, v___x_2158_, v___x_2160_);
v___x_2162_ = l_Lean_Json_mkObj(v___x_2161_);
lean_dec(v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2163_, lean_object* v_inst_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2164_, v_x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2168_, 0, lean_box(0));
lean_closure_set(v___x_2168_, 1, v_inst_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2169_, lean_object* v_inst_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2171_, 0, lean_box(0));
lean_closure_set(v___x_2171_, 1, v_inst_2170_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = 1;
v___x_2178_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2179_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2182_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2183_ = lean_string_append(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = 1;
v___x_2187_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2188_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2187_, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2190_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2191_ = lean_string_append(v___x_2190_, v___x_2189_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2194_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2195_ = lean_string_append(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = 1;
v___x_2202_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2205_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2206_ = lean_string_append(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2208_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2209_ = lean_string_append(v___x_2208_, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = 1;
v___x_2213_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2213_, v___x_2212_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2216_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2217_ = lean_string_append(v___x_2216_, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2219_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2220_ = lean_string_append(v___x_2219_, v___x_2218_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = 1;
v___x_2225_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2228_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2229_ = lean_string_append(v___x_2228_, v___x_2227_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2231_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2232_ = lean_string_append(v___x_2231_, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = 1;
v___x_2236_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2237_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2236_, v___x_2235_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2239_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2240_ = lean_string_append(v___x_2239_, v___x_2238_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2242_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2243_ = lean_string_append(v___x_2242_, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = 1;
v___x_2247_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2248_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2247_, v___x_2246_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2250_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2251_ = lean_string_append(v___x_2250_, v___x_2249_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2252_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2253_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2254_ = lean_string_append(v___x_2253_, v___x_2252_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = 1;
v___x_2258_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2258_, v___x_2257_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2261_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2262_ = lean_string_append(v___x_2261_, v___x_2260_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2264_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2265_ = lean_string_append(v___x_2264_, v___x_2263_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = 1;
v___x_2269_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2270_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2269_, v___x_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2272_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2273_ = lean_string_append(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2275_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2276_ = lean_string_append(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2277_, lean_object* v_json_2278_){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2280_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2278_);
v___x_2281_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2279_, v___x_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2291_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2291_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2286_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2287_ = lean_string_append(v___x_2286_, v_a_2282_);
lean_dec(v_a_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2287_);
v___x_2289_ = v___x_2284_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2292_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2281_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2281_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 0);
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2300_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2301_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2302_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2303_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2278_);
v___x_2304_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2301_, v___x_2303_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
v___x_2310_ = lean_string_append(v___x_2309_, v_a_2305_);
lean_dec(v_a_2305_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2310_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2315_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2304_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2304_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
lean_ctor_set_tag(v___x_2317_, 0);
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
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
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2324_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2278_);
v___x_2325_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2302_, v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2335_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2331_ = lean_string_append(v___x_2330_, v_a_2326_);
lean_dec(v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
else
{
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2336_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2325_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2325_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 0);
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2344_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2345_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2346_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2278_);
v___x_2347_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2345_, v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2357_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2352_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
v___x_2353_ = lean_string_append(v___x_2352_, v_a_2348_);
lean_dec(v_a_2348_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2353_);
v___x_2355_ = v___x_2350_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2358_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2347_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2347_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 0);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
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
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2366_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2368_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2278_);
v___x_2369_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2367_, v___x_2368_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2379_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2379_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2374_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2375_ = lean_string_append(v___x_2374_, v_a_2370_);
lean_dec(v_a_2370_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2375_);
v___x_2377_ = v___x_2372_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
else
{
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2380_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2369_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2369_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_a_2388_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2389_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2278_);
v___x_2390_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2345_, v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2395_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
v___x_2396_ = lean_string_append(v___x_2395_, v_a_2391_);
lean_dec(v_a_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2396_);
v___x_2398_ = v___x_2393_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
else
{
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2401_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2390_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2390_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 0);
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2409_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2410_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2278_);
v___x_2411_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v___x_2279_, v___x_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_a_2409_);
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2421_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2421_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2416_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
v___x_2417_ = lean_string_append(v___x_2416_, v_a_2412_);
lean_dec(v_a_2412_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2417_);
v___x_2419_ = v___x_2414_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
else
{
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_a_2409_);
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
lean_dec(v_json_2278_);
lean_dec_ref(v_inst_2277_);
v_a_2422_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2411_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2411_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set_tag(v___x_2424_, 0);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2431_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2432_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2278_, v_inst_2277_, v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2430_);
lean_dec(v_a_2409_);
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2438_ = lean_string_append(v___x_2437_, v_a_2433_);
lean_dec(v_a_2433_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_a_2430_);
lean_dec(v_a_2409_);
lean_dec(v_a_2388_);
lean_dec(v_a_2366_);
lean_dec(v_a_2344_);
lean_dec(v_a_2323_);
lean_dec(v_a_2300_);
v_a_2443_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2432_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2432_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 0);
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2462_; 
v_a_2451_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2453_ = v___x_2432_;
v_isShared_2454_ = v_isSharedCheck_2462_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2432_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2462_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; uint8_t v___x_2456_; uint8_t v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2460_; 
v___x_2455_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2455_, 0, v_a_2300_);
lean_ctor_set(v___x_2455_, 1, v_a_2323_);
lean_ctor_set(v___x_2455_, 2, v_a_2344_);
lean_ctor_set(v___x_2455_, 3, v_a_2430_);
lean_ctor_set(v___x_2455_, 4, v_a_2451_);
v___x_2456_ = lean_unbox(v_a_2366_);
lean_dec(v_a_2366_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*5, v___x_2456_);
v___x_2457_ = lean_unbox(v_a_2388_);
lean_dec(v_a_2388_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*5 + 1, v___x_2457_);
v___x_2458_ = lean_unbox(v_a_2409_);
lean_dec(v_a_2409_);
lean_ctor_set_uint8(v___x_2455_, sizeof(void*)*5 + 2, v___x_2458_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2460_ = v___x_2453_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2463_, lean_object* v_inst_2464_, lean_object* v_json_2465_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2464_, v_json_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2467_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2468_, 0, lean_box(0));
lean_closure_set(v___x_2468_, 1, v_inst_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2469_, lean_object* v_inst_2470_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2471_, 0, lean_box(0));
lean_closure_set(v___x_2471_, 1, v_inst_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2472_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
else
{
lean_object* v_val_2474_; lean_object* v___x_2475_; 
v_val_2474_ = lean_ctor_get(v_x_2472_, 0);
lean_inc(v_val_2474_);
lean_dec_ref_known(v_x_2472_, 1);
v___x_2475_ = l_Lean_instToJsonPosition_toJson(v_val_2474_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
if (lean_obj_tag(v_a_2476_) == 0)
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_array_to_list(v_a_2477_);
return v___x_2478_;
}
else
{
lean_object* v_head_2479_; lean_object* v_tail_2480_; lean_object* v___x_2481_; 
v_head_2479_ = lean_ctor_get(v_a_2476_, 0);
lean_inc(v_head_2479_);
v_tail_2480_ = lean_ctor_get(v_a_2476_, 1);
lean_inc(v_tail_2480_);
lean_dec_ref_known(v_a_2476_, 2);
v___x_2481_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2477_, v_head_2479_);
v_a_2476_ = v_tail_2480_;
v_a_2477_ = v___x_2481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2484_){
_start:
{
lean_object* v_toBaseMessage_2485_; lean_object* v_kind_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2551_; 
v_toBaseMessage_2485_ = lean_ctor_get(v_x_2484_, 0);
v_kind_2486_ = lean_ctor_get(v_x_2484_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2488_ = v_x_2484_;
v_isShared_2489_ = v_isSharedCheck_2551_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_kind_2486_);
lean_inc(v_toBaseMessage_2485_);
lean_dec(v_x_2484_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2551_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_fileName_2490_; lean_object* v_pos_2491_; lean_object* v_endPos_2492_; uint8_t v_keepFullRange_2493_; uint8_t v_severity_2494_; uint8_t v_isSilent_2495_; lean_object* v_caption_2496_; lean_object* v_data_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
v_fileName_2490_ = lean_ctor_get(v_toBaseMessage_2485_, 0);
lean_inc_ref(v_fileName_2490_);
v_pos_2491_ = lean_ctor_get(v_toBaseMessage_2485_, 1);
lean_inc_ref(v_pos_2491_);
v_endPos_2492_ = lean_ctor_get(v_toBaseMessage_2485_, 2);
lean_inc(v_endPos_2492_);
v_keepFullRange_2493_ = lean_ctor_get_uint8(v_toBaseMessage_2485_, sizeof(void*)*5);
v_severity_2494_ = lean_ctor_get_uint8(v_toBaseMessage_2485_, sizeof(void*)*5 + 1);
v_isSilent_2495_ = lean_ctor_get_uint8(v_toBaseMessage_2485_, sizeof(void*)*5 + 2);
v_caption_2496_ = lean_ctor_get(v_toBaseMessage_2485_, 3);
lean_inc_ref(v_caption_2496_);
v_data_2497_ = lean_ctor_get(v_toBaseMessage_2485_, 4);
lean_inc(v_data_2497_);
lean_dec_ref(v_toBaseMessage_2485_);
v___x_2498_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_fileName_2490_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2499_);
lean_ctor_set(v___x_2488_, 0, v___x_2498_);
v___x_2501_ = v___x_2488_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2502_ = lean_box(0);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2505_ = l_Lean_instToJsonPosition_toJson(v_pos_2491_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v___x_2502_);
v___x_2508_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2509_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2492_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v___x_2502_);
v___x_2512_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2513_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2513_, 0, v_keepFullRange_2493_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v___x_2502_);
v___x_2516_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2517_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2494_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___x_2502_);
v___x_2520_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2521_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2521_, 0, v_isSilent_2495_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___x_2502_);
v___x_2524_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_caption_2496_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v___x_2502_);
v___x_2528_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_data_2497_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2528_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___x_2502_);
v___x_2532_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2533_ = 1;
v___x_2534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2486_, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2532_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v___x_2502_);
v___x_2538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
lean_ctor_set(v___x_2538_, 1, v___x_2502_);
v___x_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2531_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2527_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2523_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2519_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2515_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2511_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2507_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2503_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2548_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2546_, v___x_2547_);
v___x_2549_ = l_Lean_Json_mkObj(v___x_2548_);
lean_dec(v___x_2548_);
return v___x_2549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2554_, lean_object* v_k_2555_){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = l_Lean_Json_getObjValD(v_j_2554_, v_k_2555_);
v___x_2557_ = l_Lean_Json_getStr_x3f(v___x_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2558_, lean_object* v_k_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2558_, v_k_2559_);
lean_dec_ref(v_k_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2561_, lean_object* v_k_2562_){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = l_Lean_Json_getObjValD(v_j_2561_, v_k_2562_);
v___x_2564_ = l_Lean_instFromJsonPosition_fromJson(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2565_, lean_object* v_k_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2565_, v_k_2566_);
lean_dec_ref(v_k_2566_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2568_, lean_object* v_k_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = l_Lean_Json_getObjValD(v_j_2568_, v_k_2569_);
v___x_2571_ = l_Lean_Json_getBool_x3f(v___x_2570_);
lean_dec(v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2572_, lean_object* v_k_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2572_, v_k_2573_);
lean_dec_ref(v_k_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2575_, lean_object* v_k_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = l_Lean_Json_getObjValD(v_j_2575_, v_k_2576_);
v___x_2578_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2579_, lean_object* v_k_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2579_, v_k_2580_);
lean_dec_ref(v_k_2580_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2582_, lean_object* v_k_2583_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = l_Lean_Json_getObjValD(v_j_2582_, v_k_2583_);
v___x_2585_ = l_Lean_Name_fromJson_x3f(v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2586_, lean_object* v_k_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2586_, v_k_2587_);
lean_dec_ref(v_k_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2591_){
_start:
{
if (lean_obj_tag(v_x_2591_) == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_instFromJsonPosition_fromJson(v_x_2591_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
v_a_2602_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2604_ = v___x_2593_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2593_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_a_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2611_, lean_object* v_k_2612_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = l_Lean_Json_getObjValD(v_j_2611_, v_k_2612_);
v___x_2614_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2615_, v_k_2616_);
lean_dec_ref(v_k_2616_);
return v_res_2617_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2622_ = 1;
v___x_2623_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2623_, v___x_2622_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2625_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2626_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2627_ = lean_string_append(v___x_2626_, v___x_2625_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2628_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2629_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2630_ = lean_string_append(v___x_2629_, v___x_2628_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2632_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2633_ = lean_string_append(v___x_2632_, v___x_2631_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2635_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2636_ = lean_string_append(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2639_ = lean_string_append(v___x_2638_, v___x_2637_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2641_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2642_ = lean_string_append(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2643_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2644_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2645_ = lean_string_append(v___x_2644_, v___x_2643_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2647_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2648_ = lean_string_append(v___x_2647_, v___x_2646_);
return v___x_2648_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2650_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2651_ = lean_string_append(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2652_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2653_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2654_ = lean_string_append(v___x_2653_, v___x_2652_);
return v___x_2654_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2655_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2656_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2657_ = lean_string_append(v___x_2656_, v___x_2655_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2659_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2660_ = lean_string_append(v___x_2659_, v___x_2658_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2662_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2663_ = lean_string_append(v___x_2662_, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2665_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2666_ = lean_string_append(v___x_2665_, v___x_2664_);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2668_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2669_ = lean_string_append(v___x_2668_, v___x_2667_);
return v___x_2669_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2671_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2672_ = lean_string_append(v___x_2671_, v___x_2670_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2674_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2675_ = lean_string_append(v___x_2674_, v___x_2673_);
return v___x_2675_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = 1;
v___x_2679_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2682_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2683_ = lean_string_append(v___x_2682_, v___x_2681_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2685_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2686_ = lean_string_append(v___x_2685_, v___x_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2687_);
v___x_2689_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2687_, v___x_2688_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_json_2687_);
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2699_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2694_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
v___x_2695_ = lean_string_append(v___x_2694_, v_a_2690_);
lean_dec(v_a_2690_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2695_);
v___x_2697_ = v___x_2692_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
else
{
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_json_2687_);
v_a_2700_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2689_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2689_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
lean_ctor_set_tag(v___x_2702_, 0);
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v_a_2708_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2709_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2687_);
v___x_2710_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2687_, v___x_2709_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2720_; 
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2720_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2716_ = lean_string_append(v___x_2715_, v_a_2711_);
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v___x_2716_);
v___x_2718_ = v___x_2713_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2721_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2710_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2710_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
lean_ctor_set_tag(v___x_2723_, 0);
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_a_2729_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2730_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2687_);
v___x_2731_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2687_, v___x_2730_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2741_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2736_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2737_ = lean_string_append(v___x_2736_, v_a_2732_);
lean_dec(v_a_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2737_);
v___x_2739_ = v___x_2734_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
else
{
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2742_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2731_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2731_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 0);
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2750_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2751_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2687_);
v___x_2752_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2687_, v___x_2751_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2762_; 
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2762_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2762_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2757_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2758_ = lean_string_append(v___x_2757_, v_a_2753_);
lean_dec(v_a_2753_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2758_);
v___x_2760_ = v___x_2755_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
else
{
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2770_; 
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2763_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2765_ = v___x_2752_;
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2752_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2770_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2768_; 
if (v_isShared_2766_ == 0)
{
lean_ctor_set_tag(v___x_2765_, 0);
v___x_2768_ = v___x_2765_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_a_2771_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2772_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2687_);
v___x_2773_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2687_, v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2783_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2783_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2779_ = lean_string_append(v___x_2778_, v_a_2774_);
lean_dec(v_a_2774_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2779_);
v___x_2781_ = v___x_2776_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
else
{
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2784_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2773_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2773_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 0);
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2793_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2687_);
v___x_2794_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2687_, v___x_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2804_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2804_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2799_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2800_ = lean_string_append(v___x_2799_, v_a_2795_);
lean_dec(v_a_2795_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2800_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
else
{
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2805_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2794_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2794_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 0);
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
v_a_2813_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2814_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2687_);
v___x_2815_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2687_, v___x_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2825_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2820_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2821_ = lean_string_append(v___x_2820_, v_a_2816_);
lean_dec(v_a_2816_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2821_);
v___x_2823_ = v___x_2818_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
else
{
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2826_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2815_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2815_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 0);
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_a_2834_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2835_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2687_);
v___x_2836_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2687_, v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2834_);
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2846_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2841_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2842_ = lean_string_append(v___x_2841_, v_a_2837_);
lean_dec(v_a_2837_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2842_);
v___x_2844_ = v___x_2839_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2834_);
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
lean_dec(v_json_2687_);
v_a_2847_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2836_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2836_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
lean_ctor_set_tag(v___x_2849_, 0);
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2855_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2856_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2857_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2687_, v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2834_);
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2860_ = v___x_2857_;
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2865_; 
v___x_2862_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2863_ = lean_string_append(v___x_2862_, v_a_2858_);
lean_dec(v_a_2858_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2863_);
v___x_2865_ = v___x_2860_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
else
{
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2834_);
lean_dec(v_a_2813_);
lean_dec(v_a_2792_);
lean_dec(v_a_2771_);
lean_dec(v_a_2750_);
lean_dec(v_a_2729_);
lean_dec(v_a_2708_);
v_a_2868_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2857_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2857_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 0);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2888_; 
v_a_2876_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2878_ = v___x_2857_;
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2857_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2888_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; uint8_t v___x_2881_; uint8_t v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2880_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2880_, 0, v_a_2708_);
lean_ctor_set(v___x_2880_, 1, v_a_2729_);
lean_ctor_set(v___x_2880_, 2, v_a_2750_);
lean_ctor_set(v___x_2880_, 3, v_a_2834_);
lean_ctor_set(v___x_2880_, 4, v_a_2855_);
v___x_2881_ = lean_unbox(v_a_2771_);
lean_dec(v_a_2771_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*5, v___x_2881_);
v___x_2882_ = lean_unbox(v_a_2792_);
lean_dec(v_a_2792_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*5 + 1, v___x_2882_);
v___x_2883_ = lean_unbox(v_a_2813_);
lean_dec(v_a_2813_);
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*5 + 2, v___x_2883_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2880_);
lean_ctor_set(v___x_2884_, 1, v_a_2876_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2884_);
v___x_2886_ = v___x_2878_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2895_ = l_Lean_Name_str___override(v_errorName_2893_, v___x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2896_, lean_object* v_name_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = l_Lean_kindOfErrorName(v_name_2897_);
v___x_2899_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v_msg_2896_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2901_){
_start:
{
switch(lean_obj_tag(v_a_2901_))
{
case 0:
{
return v_a_2901_;
}
case 1:
{
lean_object* v_pre_2902_; lean_object* v_str_2903_; lean_object* v_p_x27_2904_; uint8_t v___y_2906_; uint8_t v___x_2909_; 
v_pre_2902_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_pre_2902_);
v_str_2903_ = lean_ctor_get(v_a_2901_, 1);
lean_inc_ref(v_str_2903_);
lean_dec_ref_known(v_a_2901_, 2);
v_p_x27_2904_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2902_);
v___x_2909_ = l_Lean_Name_isAnonymous(v_p_x27_2904_);
if (v___x_2909_ == 0)
{
v___y_2906_ = v___x_2909_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2911_ = lean_string_dec_eq(v_str_2903_, v___x_2910_);
v___y_2906_ = v___x_2911_;
goto v___jp_2905_;
}
v___jp_2905_:
{
if (v___y_2906_ == 0)
{
lean_object* v___x_2907_; 
v___x_2907_ = l_Lean_Name_str___override(v_p_x27_2904_, v_str_2903_);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; 
lean_dec(v_p_x27_2904_);
lean_dec_ref(v_str_2903_);
v___x_2908_ = lean_box(0);
return v___x_2908_;
}
}
}
default: 
{
lean_object* v_pre_2912_; lean_object* v_i_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v_pre_2912_ = lean_ctor_get(v_a_2901_, 0);
lean_inc(v_pre_2912_);
v_i_2913_ = lean_ctor_get(v_a_2901_, 1);
lean_inc(v_i_2913_);
lean_dec_ref_known(v_a_2901_, 2);
v___x_2914_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2912_);
v___x_2915_ = l_Lean_Name_num___override(v___x_2914_, v_i_2913_);
return v___x_2915_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2916_){
_start:
{
switch(lean_obj_tag(v_x_2916_))
{
case 3:
{
lean_object* v_a_2917_; lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2926_; 
v_a_2917_ = lean_ctor_get(v_x_2916_, 0);
v_a_2918_ = lean_ctor_get(v_x_2916_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_x_2916_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2920_ = v_x_2916_;
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_inc(v_a_2917_);
lean_dec(v_x_2916_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2926_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2922_ = l_Lean_MessageData_stripNestedTags(v_a_2918_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 1, v___x_2922_);
v___x_2924_ = v___x_2920_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2917_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
case 4:
{
lean_object* v_a_2927_; lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2936_; 
v_a_2927_ = lean_ctor_get(v_x_2916_, 0);
v_a_2928_ = lean_ctor_get(v_x_2916_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_x_2916_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2930_ = v_x_2916_;
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_inc(v_a_2927_);
lean_dec(v_x_2916_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = l_Lean_MessageData_stripNestedTags(v_a_2928_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 1, v___x_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2927_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
case 8:
{
lean_object* v_a_2937_; lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2946_; 
v_a_2937_ = lean_ctor_get(v_x_2916_, 0);
v_a_2938_ = lean_ctor_get(v_x_2916_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v_x_2916_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2940_ = v_x_2916_;
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_inc(v_a_2937_);
lean_dec(v_x_2916_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2946_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2937_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2942_);
v___x_2944_ = v___x_2940_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2938_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
case 11:
{
lean_object* v_a_2947_; lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2956_; 
v_a_2947_ = lean_ctor_get(v_x_2916_, 0);
v_a_2948_ = lean_ctor_get(v_x_2916_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_x_2916_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2950_ = v_x_2916_;
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_inc(v_a_2947_);
lean_dec(v_x_2916_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2956_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = l_Lean_MessageData_stripNestedTags(v_a_2948_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2947_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
default: 
{
return v_x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2957_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 1)
{
lean_object* v_pre_2958_; lean_object* v_str_2959_; lean_object* v___x_2960_; uint8_t v___x_2961_; 
v_pre_2958_ = lean_ctor_get(v_x_2957_, 0);
v_str_2959_ = lean_ctor_get(v_x_2957_, 1);
v___x_2960_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2961_ = lean_string_dec_eq(v_str_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_box(0);
return v___x_2962_;
}
else
{
lean_object* v___x_2963_; 
lean_inc(v_pre_2958_);
v___x_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_pre_2958_);
return v___x_2963_;
}
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_box(0);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_errorNameOfKind_x3f(v_x_2965_);
lean_dec(v_x_2965_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = l_Lean_MessageData_kind(v_msg_2967_);
v___x_2969_ = l_Lean_errorNameOfKind_x3f(v___x_2968_);
lean_dec(v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lean_MessageData_errorName_x3f(v_msg_2970_);
lean_dec_ref(v_msg_2970_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2972_){
_start:
{
lean_object* v_data_2973_; lean_object* v___x_2974_; 
v_data_2973_ = lean_ctor_get(v_msg_2972_, 4);
v___x_2974_ = l_Lean_MessageData_errorName_x3f(v_data_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Message_errorName_x3f(v_msg_2975_);
lean_dec_ref(v_msg_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2977_){
_start:
{
lean_object* v_toBaseMessage_2978_; lean_object* v_fileName_2979_; lean_object* v_pos_2980_; lean_object* v_endPos_2981_; uint8_t v_keepFullRange_2982_; uint8_t v_severity_2983_; uint8_t v_isSilent_2984_; lean_object* v_caption_2985_; lean_object* v_data_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2995_; 
v_toBaseMessage_2978_ = lean_ctor_get(v_msg_2977_, 0);
lean_inc_ref(v_toBaseMessage_2978_);
lean_dec_ref(v_msg_2977_);
v_fileName_2979_ = lean_ctor_get(v_toBaseMessage_2978_, 0);
v_pos_2980_ = lean_ctor_get(v_toBaseMessage_2978_, 1);
v_endPos_2981_ = lean_ctor_get(v_toBaseMessage_2978_, 2);
v_keepFullRange_2982_ = lean_ctor_get_uint8(v_toBaseMessage_2978_, sizeof(void*)*5);
v_severity_2983_ = lean_ctor_get_uint8(v_toBaseMessage_2978_, sizeof(void*)*5 + 1);
v_isSilent_2984_ = lean_ctor_get_uint8(v_toBaseMessage_2978_, sizeof(void*)*5 + 2);
v_caption_2985_ = lean_ctor_get(v_toBaseMessage_2978_, 3);
v_data_2986_ = lean_ctor_get(v_toBaseMessage_2978_, 4);
v_isSharedCheck_2995_ = !lean_is_exclusive(v_toBaseMessage_2978_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2988_ = v_toBaseMessage_2978_;
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_data_2986_);
lean_inc(v_caption_2985_);
lean_inc(v_endPos_2981_);
lean_inc(v_pos_2980_);
lean_inc(v_fileName_2979_);
lean_dec(v_toBaseMessage_2978_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2995_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_data_2986_);
v___x_2991_ = l_Lean_MessageData_ofFormat(v___x_2990_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 4, v___x_2991_);
v___x_2993_ = v___x_2988_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_fileName_2979_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v_pos_2980_);
lean_ctor_set(v_reuseFailAlloc_2994_, 2, v_endPos_2981_);
lean_ctor_set(v_reuseFailAlloc_2994_, 3, v_caption_2985_);
lean_ctor_set(v_reuseFailAlloc_2994_, 4, v___x_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_2994_, sizeof(void*)*5, v_keepFullRange_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2994_, sizeof(void*)*5 + 1, v_severity_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2994_, sizeof(void*)*5 + 2, v_isSilent_2984_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_3001_, uint8_t v_includeEndPos_3002_){
_start:
{
lean_object* v___y_3004_; lean_object* v___y_3008_; uint32_t v___y_3009_; lean_object* v___y_3013_; lean_object* v_str_3016_; lean_object* v_toBaseMessage_3026_; lean_object* v_kind_3027_; lean_object* v_fileName_3028_; lean_object* v_pos_3029_; lean_object* v_endPos_3030_; uint8_t v_severity_3031_; lean_object* v_caption_3032_; lean_object* v_data_3033_; lean_object* v___y_3035_; lean_object* v_str_3036_; lean_object* v___y_3044_; 
v_toBaseMessage_3026_ = lean_ctor_get(v_msg_3001_, 0);
lean_inc_ref(v_toBaseMessage_3026_);
v_kind_3027_ = lean_ctor_get(v_msg_3001_, 1);
lean_inc(v_kind_3027_);
lean_dec_ref(v_msg_3001_);
v_fileName_3028_ = lean_ctor_get(v_toBaseMessage_3026_, 0);
lean_inc_ref(v_fileName_3028_);
v_pos_3029_ = lean_ctor_get(v_toBaseMessage_3026_, 1);
lean_inc_ref(v_pos_3029_);
v_endPos_3030_ = lean_ctor_get(v_toBaseMessage_3026_, 2);
lean_inc(v_endPos_3030_);
v_severity_3031_ = lean_ctor_get_uint8(v_toBaseMessage_3026_, sizeof(void*)*5 + 1);
v_caption_3032_ = lean_ctor_get(v_toBaseMessage_3026_, 3);
lean_inc_ref(v_caption_3032_);
v_data_3033_ = lean_ctor_get(v_toBaseMessage_3026_, 4);
lean_inc(v_data_3033_);
lean_dec_ref(v_toBaseMessage_3026_);
if (v_includeEndPos_3002_ == 0)
{
lean_object* v___x_3050_; 
lean_dec(v_endPos_3030_);
v___x_3050_ = lean_box(0);
v___y_3044_ = v___x_3050_;
goto v___jp_3043_;
}
else
{
v___y_3044_ = v_endPos_3030_;
goto v___jp_3043_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v_str_3006_; 
v___x_3005_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3006_ = lean_string_append(v___y_3004_, v___x_3005_);
return v_str_3006_;
}
v___jp_3007_:
{
uint32_t v___x_3010_; uint8_t v___x_3011_; 
v___x_3010_ = 10;
v___x_3011_ = lean_uint32_dec_eq(v___y_3009_, v___x_3010_);
if (v___x_3011_ == 0)
{
v___y_3004_ = v___y_3008_;
goto v___jp_3003_;
}
else
{
return v___y_3008_;
}
}
v___jp_3012_:
{
uint32_t v___x_3014_; 
v___x_3014_ = 65;
v___y_3008_ = v___y_3013_;
v___y_3009_ = v___x_3014_;
goto v___jp_3007_;
}
v___jp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3017_ = lean_string_utf8_byte_size(v_str_3016_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v___x_3019_ = lean_nat_dec_eq(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_inc_ref(v_str_3016_);
v___x_3020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3020_, 0, v_str_3016_);
lean_ctor_set(v___x_3020_, 1, v___x_3018_);
lean_ctor_set(v___x_3020_, 2, v___x_3017_);
v___x_3021_ = l_String_Slice_Pos_prev_x3f(v___x_3020_, v___x_3017_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec_ref_known(v___x_3020_, 3);
v___y_3013_ = v_str_3016_;
goto v___jp_3012_;
}
else
{
lean_object* v_val_3022_; lean_object* v___x_3023_; 
v_val_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = l_String_Slice_Pos_get_x3f(v___x_3020_, v_val_3022_);
lean_dec(v_val_3022_);
lean_dec_ref_known(v___x_3020_, 3);
if (lean_obj_tag(v___x_3023_) == 0)
{
v___y_3013_ = v_str_3016_;
goto v___jp_3012_;
}
else
{
lean_object* v_val_3024_; uint32_t v___x_3025_; 
v_val_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_val_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = lean_unbox_uint32(v_val_3024_);
lean_dec(v_val_3024_);
v___y_3008_ = v_str_3016_;
v___y_3009_ = v___x_3025_;
goto v___jp_3007_;
}
}
}
else
{
v___y_3004_ = v_str_3016_;
goto v___jp_3003_;
}
}
v___jp_3034_:
{
switch(v_severity_3031_)
{
case 0:
{
lean_dec(v___y_3035_);
lean_dec_ref(v_pos_3029_);
lean_dec_ref(v_fileName_3028_);
lean_dec(v_kind_3027_);
v_str_3016_ = v_str_3036_;
goto v___jp_3015_;
}
case 1:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v_str_3039_; 
v___x_3037_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3038_ = l_Lean_errorNameOfKind_x3f(v_kind_3027_);
lean_dec(v_kind_3027_);
v_str_3039_ = l_Lean_mkErrorStringWithPos(v_fileName_3028_, v_pos_3029_, v_str_3036_, v___y_3035_, v___x_3037_, v___x_3038_);
lean_dec_ref(v_str_3036_);
v_str_3016_ = v_str_3039_;
goto v___jp_3015_;
}
default: 
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v_str_3042_; 
v___x_3040_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3041_ = l_Lean_errorNameOfKind_x3f(v_kind_3027_);
lean_dec(v_kind_3027_);
v_str_3042_ = l_Lean_mkErrorStringWithPos(v_fileName_3028_, v_pos_3029_, v_str_3036_, v___y_3035_, v___x_3040_, v___x_3041_);
lean_dec_ref(v_str_3036_);
v_str_3016_ = v_str_3042_;
goto v___jp_3015_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3046_ = lean_string_dec_eq(v_caption_3032_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_str_3049_; 
v___x_3047_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3048_ = lean_string_append(v_caption_3032_, v___x_3047_);
v_str_3049_ = lean_string_append(v___x_3048_, v_data_3033_);
lean_dec(v_data_3033_);
v___y_3035_ = v___y_3044_;
v_str_3036_ = v_str_3049_;
goto v___jp_3034_;
}
else
{
lean_dec_ref(v_caption_3032_);
v___y_3035_ = v___y_3044_;
v_str_3036_ = v_data_3033_;
goto v___jp_3034_;
}
}
}
}
LEAN_EXPORT void l_Lean_SerialMessage_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3001_ = stack[0].m_obj;
uint8_t v_includeEndPos_3002_ = stack[1].m_num;
lean_object* v_res_3051_;
v_res_3051_ = l_Lean_SerialMessage_toString(v_msg_3001_, v_includeEndPos_3002_);
stack->m_obj
 = v_res_3051_;
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3052_, lean_object* v_includeEndPos_3053_){
_start:
{
uint8_t v_includeEndPos_boxed_3054_; lean_object* v_res_3055_; 
v_includeEndPos_boxed_3054_ = lean_unbox(v_includeEndPos_3053_);
v_res_3055_ = l_Lean_SerialMessage_toString(v_msg_3052_, v_includeEndPos_boxed_3054_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3056_){
_start:
{
uint8_t v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = 0;
v___x_3058_ = l_Lean_SerialMessage_toString(v_msg_3056_, v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3061_){
_start:
{
lean_object* v_data_3062_; lean_object* v___x_3063_; 
v_data_3062_ = lean_ctor_get(v_msg_3061_, 4);
v___x_3063_ = l_Lean_MessageData_kind(v_data_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_Message_kind(v_msg_3064_);
lean_dec_ref(v_msg_3064_);
return v_res_3065_;
}
}
uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3066_){
_start:
{
lean_object* v_data_3067_; uint8_t v___x_3068_; 
v_data_3067_ = lean_ctor_get(v_msg_3066_, 4);
v___x_3068_ = l_Lean_MessageData_isTrace(v_data_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT void l_Lean_Message_isTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3066_ = stack[0].m_obj;
uint8_t v_res_3069_;
v_res_3069_ = l_Lean_Message_isTrace(v_msg_3066_);
stack->m_num = v_res_3069_;
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3070_){
_start:
{
uint8_t v_res_3071_; lean_object* v_r_3072_; 
v_res_3071_ = l_Lean_Message_isTrace(v_msg_3070_);
lean_dec_ref(v_msg_3070_);
v_r_3072_ = lean_box(v_res_3071_);
return v_r_3072_;
}
}
lean_object* l_Lean_Message_serialize(lean_object* v_msg_3073_){
_start:
{
lean_object* v_fileName_3075_; lean_object* v_pos_3076_; lean_object* v_endPos_3077_; uint8_t v_keepFullRange_3078_; uint8_t v_severity_3079_; uint8_t v_isSilent_3080_; lean_object* v_caption_3081_; lean_object* v_data_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3092_; 
v_fileName_3075_ = lean_ctor_get(v_msg_3073_, 0);
v_pos_3076_ = lean_ctor_get(v_msg_3073_, 1);
v_endPos_3077_ = lean_ctor_get(v_msg_3073_, 2);
v_keepFullRange_3078_ = lean_ctor_get_uint8(v_msg_3073_, sizeof(void*)*5);
v_severity_3079_ = lean_ctor_get_uint8(v_msg_3073_, sizeof(void*)*5 + 1);
v_isSilent_3080_ = lean_ctor_get_uint8(v_msg_3073_, sizeof(void*)*5 + 2);
v_caption_3081_ = lean_ctor_get(v_msg_3073_, 3);
v_data_3082_ = lean_ctor_get(v_msg_3073_, 4);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_msg_3073_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3084_ = v_msg_3073_;
v_isShared_3085_ = v_isSharedCheck_3092_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_data_3082_);
lean_inc(v_caption_3081_);
lean_inc(v_endPos_3077_);
lean_inc(v_pos_3076_);
lean_inc(v_fileName_3075_);
lean_dec(v_msg_3073_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3092_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
lean_inc(v_data_3082_);
v___x_3086_ = l_Lean_MessageData_toString(v_data_3082_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 4, v___x_3086_);
v___x_3088_ = v___x_3084_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_fileName_3075_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_pos_3076_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_endPos_3077_);
lean_ctor_set(v_reuseFailAlloc_3091_, 3, v_caption_3081_);
lean_ctor_set(v_reuseFailAlloc_3091_, 4, v___x_3086_);
lean_ctor_set_uint8(v_reuseFailAlloc_3091_, sizeof(void*)*5, v_keepFullRange_3078_);
lean_ctor_set_uint8(v_reuseFailAlloc_3091_, sizeof(void*)*5 + 1, v_severity_3079_);
lean_ctor_set_uint8(v_reuseFailAlloc_3091_, sizeof(void*)*5 + 2, v_isSilent_3080_);
v___x_3088_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = l_Lean_MessageData_kind(v_data_3082_);
lean_dec(v_data_3082_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT void l_Lean_Message_serialize_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3073_ = stack[0].m_obj;
lean_object* v_res_3093_;
v_res_3093_ = l_Lean_Message_serialize(v_msg_3073_);
stack->m_obj
 = v_res_3093_;
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_Lean_Message_serialize(v_msg_3094_);
return v_res_3096_;
}
}
lean_object* l_Lean_Message_toString(lean_object* v_msg_3097_, uint8_t v_includeEndPos_3098_){
_start:
{
lean_object* v_fileName_3100_; lean_object* v_pos_3101_; lean_object* v_endPos_3102_; uint8_t v_severity_3103_; lean_object* v_caption_3104_; lean_object* v_data_3105_; lean_object* v___x_3106_; lean_object* v___y_3108_; lean_object* v___y_3112_; uint32_t v___y_3113_; lean_object* v___y_3117_; lean_object* v_str_3120_; lean_object* v___x_3130_; lean_object* v___y_3132_; lean_object* v_str_3133_; lean_object* v___y_3141_; 
v_fileName_3100_ = lean_ctor_get(v_msg_3097_, 0);
lean_inc_ref(v_fileName_3100_);
v_pos_3101_ = lean_ctor_get(v_msg_3097_, 1);
lean_inc_ref(v_pos_3101_);
v_endPos_3102_ = lean_ctor_get(v_msg_3097_, 2);
lean_inc(v_endPos_3102_);
v_severity_3103_ = lean_ctor_get_uint8(v_msg_3097_, sizeof(void*)*5 + 1);
v_caption_3104_ = lean_ctor_get(v_msg_3097_, 3);
lean_inc_ref(v_caption_3104_);
v_data_3105_ = lean_ctor_get(v_msg_3097_, 4);
lean_inc_n(v_data_3105_, 2);
lean_dec_ref(v_msg_3097_);
v___x_3106_ = l_Lean_MessageData_toString(v_data_3105_);
v___x_3130_ = l_Lean_MessageData_kind(v_data_3105_);
lean_dec(v_data_3105_);
if (v_includeEndPos_3098_ == 0)
{
lean_object* v___x_3147_; 
lean_dec(v_endPos_3102_);
v___x_3147_ = lean_box(0);
v___y_3141_ = v___x_3147_;
goto v___jp_3140_;
}
else
{
v___y_3141_ = v_endPos_3102_;
goto v___jp_3140_;
}
v___jp_3107_:
{
lean_object* v___x_3109_; lean_object* v_str_3110_; 
v___x_3109_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3110_ = lean_string_append(v___y_3108_, v___x_3109_);
return v_str_3110_;
}
v___jp_3111_:
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 10;
v___x_3115_ = lean_uint32_dec_eq(v___y_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
v___y_3108_ = v___y_3112_;
goto v___jp_3107_;
}
else
{
return v___y_3112_;
}
}
v___jp_3116_:
{
uint32_t v___x_3118_; 
v___x_3118_ = 65;
v___y_3112_ = v___y_3117_;
v___y_3113_ = v___x_3118_;
goto v___jp_3111_;
}
v___jp_3119_:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3121_ = lean_string_utf8_byte_size(v_str_3120_);
v___x_3122_ = lean_unsigned_to_nat(0u);
v___x_3123_ = lean_nat_dec_eq(v___x_3121_, v___x_3122_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
lean_inc_ref(v_str_3120_);
v___x_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3124_, 0, v_str_3120_);
lean_ctor_set(v___x_3124_, 1, v___x_3122_);
lean_ctor_set(v___x_3124_, 2, v___x_3121_);
v___x_3125_ = l_String_Slice_Pos_prev_x3f(v___x_3124_, v___x_3121_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_dec_ref_known(v___x_3124_, 3);
v___y_3117_ = v_str_3120_;
goto v___jp_3116_;
}
else
{
lean_object* v_val_3126_; lean_object* v___x_3127_; 
v_val_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v___x_3127_ = l_String_Slice_Pos_get_x3f(v___x_3124_, v_val_3126_);
lean_dec(v_val_3126_);
lean_dec_ref_known(v___x_3124_, 3);
if (lean_obj_tag(v___x_3127_) == 0)
{
v___y_3117_ = v_str_3120_;
goto v___jp_3116_;
}
else
{
lean_object* v_val_3128_; uint32_t v___x_3129_; 
v_val_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_val_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3129_ = lean_unbox_uint32(v_val_3128_);
lean_dec(v_val_3128_);
v___y_3112_ = v_str_3120_;
v___y_3113_ = v___x_3129_;
goto v___jp_3111_;
}
}
}
else
{
v___y_3108_ = v_str_3120_;
goto v___jp_3107_;
}
}
v___jp_3131_:
{
switch(v_severity_3103_)
{
case 0:
{
lean_dec(v___y_3132_);
lean_dec(v___x_3130_);
lean_dec_ref(v_pos_3101_);
lean_dec_ref(v_fileName_3100_);
v_str_3120_ = v_str_3133_;
goto v___jp_3119_;
}
case 1:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v_str_3136_; 
v___x_3134_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3135_ = l_Lean_errorNameOfKind_x3f(v___x_3130_);
lean_dec(v___x_3130_);
v_str_3136_ = l_Lean_mkErrorStringWithPos(v_fileName_3100_, v_pos_3101_, v_str_3133_, v___y_3132_, v___x_3134_, v___x_3135_);
lean_dec_ref(v_str_3133_);
v_str_3120_ = v_str_3136_;
goto v___jp_3119_;
}
default: 
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v_str_3139_; 
v___x_3137_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3138_ = l_Lean_errorNameOfKind_x3f(v___x_3130_);
lean_dec(v___x_3130_);
v_str_3139_ = l_Lean_mkErrorStringWithPos(v_fileName_3100_, v_pos_3101_, v_str_3133_, v___y_3132_, v___x_3137_, v___x_3138_);
lean_dec_ref(v_str_3133_);
v_str_3120_ = v_str_3139_;
goto v___jp_3119_;
}
}
}
v___jp_3140_:
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3143_ = lean_string_dec_eq(v_caption_3104_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_str_3146_; 
v___x_3144_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3145_ = lean_string_append(v_caption_3104_, v___x_3144_);
v_str_3146_ = lean_string_append(v___x_3145_, v___x_3106_);
lean_dec_ref(v___x_3106_);
v___y_3132_ = v___y_3141_;
v_str_3133_ = v_str_3146_;
goto v___jp_3131_;
}
else
{
lean_dec_ref(v_caption_3104_);
v___y_3132_ = v___y_3141_;
v_str_3133_ = v___x_3106_;
goto v___jp_3131_;
}
}
}
}
LEAN_EXPORT void l_Lean_Message_toString_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3097_ = stack[0].m_obj;
uint8_t v_includeEndPos_3098_ = stack[1].m_num;
lean_object* v_res_3148_;
v_res_3148_ = l_Lean_Message_toString(v_msg_3097_, v_includeEndPos_3098_);
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3149_, lean_object* v_includeEndPos_3150_, lean_object* v_a_3151_){
_start:
{
uint8_t v_includeEndPos_boxed_3152_; lean_object* v_res_3153_; 
v_includeEndPos_boxed_3152_ = lean_unbox(v_includeEndPos_3150_);
v_res_3153_ = l_Lean_Message_toString(v_msg_3149_, v_includeEndPos_boxed_3152_);
return v_res_3153_;
}
}
lean_object* l_Lean_Message_toJson(lean_object* v_msg_3154_){
_start:
{
lean_object* v_fileName_3156_; lean_object* v_pos_3157_; lean_object* v_endPos_3158_; uint8_t v_keepFullRange_3159_; uint8_t v_severity_3160_; uint8_t v_isSilent_3161_; lean_object* v_caption_3162_; lean_object* v_data_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v_fileName_3156_ = lean_ctor_get(v_msg_3154_, 0);
lean_inc_ref(v_fileName_3156_);
v_pos_3157_ = lean_ctor_get(v_msg_3154_, 1);
lean_inc_ref(v_pos_3157_);
v_endPos_3158_ = lean_ctor_get(v_msg_3154_, 2);
lean_inc(v_endPos_3158_);
v_keepFullRange_3159_ = lean_ctor_get_uint8(v_msg_3154_, sizeof(void*)*5);
v_severity_3160_ = lean_ctor_get_uint8(v_msg_3154_, sizeof(void*)*5 + 1);
v_isSilent_3161_ = lean_ctor_get_uint8(v_msg_3154_, sizeof(void*)*5 + 2);
v_caption_3162_ = lean_ctor_get(v_msg_3154_, 3);
lean_inc_ref(v_caption_3162_);
v_data_3163_ = lean_ctor_get(v_msg_3154_, 4);
lean_inc_n(v_data_3163_, 2);
lean_dec_ref(v_msg_3154_);
v___x_3164_ = l_Lean_MessageData_toString(v_data_3163_);
v___x_3165_ = l_Lean_MessageData_kind(v_data_3163_);
lean_dec(v_data_3163_);
v___x_3166_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_fileName_3156_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3166_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = lean_box(0);
v___x_3170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3168_);
lean_ctor_set(v___x_3170_, 1, v___x_3169_);
v___x_3171_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3172_ = l_Lean_instToJsonPosition_toJson(v_pos_3157_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3169_);
v___x_3175_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3176_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3158_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3175_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___x_3169_);
v___x_3179_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3180_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3180_, 0, v_keepFullRange_3159_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3179_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v___x_3169_);
v___x_3183_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3184_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3160_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3183_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___x_3169_);
v___x_3187_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3188_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3188_, 0, v_isSilent_3161_);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3169_);
v___x_3191_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_caption_3162_);
v___x_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3191_);
lean_ctor_set(v___x_3193_, 1, v___x_3192_);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v___x_3169_);
v___x_3195_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3164_);
v___x_3197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___x_3169_);
v___x_3199_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3200_ = 1;
v___x_3201_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3165_, v___x_3200_);
v___x_3202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3199_);
lean_ctor_set(v___x_3203_, 1, v___x_3202_);
v___x_3204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3169_);
v___x_3205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
lean_ctor_set(v___x_3205_, 1, v___x_3169_);
v___x_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3198_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3194_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3190_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3186_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3182_);
lean_ctor_set(v___x_3210_, 1, v___x_3209_);
v___x_3211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3178_);
lean_ctor_set(v___x_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3174_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3170_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3215_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3213_, v___x_3214_);
v___x_3216_ = l_Lean_Json_mkObj(v___x_3215_);
lean_dec(v___x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT void l_Lean_Message_toJson_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3154_ = stack[0].m_obj;
lean_object* v_res_3217_;
v_res_3217_ = l_Lean_Message_toJson(v_msg_3154_);
stack->m_obj
 = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_Message_toJson(v_msg_3218_);
return v_res_3220_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_unsigned_to_nat(32u);
v___x_3222_ = lean_mk_empty_array_with_capacity(v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3224_ = ((size_t)5ULL);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = lean_unsigned_to_nat(32u);
v___x_3227_ = lean_mk_empty_array_with_capacity(v___x_3226_);
v___x_3228_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3229_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3227_);
lean_ctor_set(v___x_3229_, 2, v___x_3225_);
lean_ctor_set(v___x_3229_, 3, v___x_3225_);
lean_ctor_set_usize(v___x_3229_, 4, v___x_3224_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = l_Lean_NameSet_empty;
v___x_3231_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
lean_ctor_set(v___x_3232_, 2, v___x_3230_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3233_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_unsigned_to_nat(32u);
v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
lean_dec_ref(v___x_3236_);
v___x_3237_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3238_){
_start:
{
lean_object* v_unreported_3239_; 
v_unreported_3239_ = lean_ctor_get(v_self_3238_, 1);
lean_inc_ref(v_unreported_3239_);
return v_unreported_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l_Lean_MessageLog_msgs(v_self_3240_);
lean_dec_ref(v_self_3240_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3242_){
_start:
{
lean_object* v_reported_3243_; lean_object* v_unreported_3244_; lean_object* v___x_3245_; 
v_reported_3243_ = lean_ctor_get(v_x_3242_, 0);
lean_inc_ref(v_reported_3243_);
v_unreported_3244_ = lean_ctor_get(v_x_3242_, 1);
lean_inc_ref(v_unreported_3244_);
lean_dec_ref(v_x_3242_);
v___x_3245_ = l_Lean_PersistentArray_append___redArg(v_reported_3243_, v_unreported_3244_);
lean_dec_ref(v_unreported_3244_);
return v___x_3245_;
}
}
uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3246_){
_start:
{
lean_object* v_unreported_3247_; uint8_t v___x_3248_; 
v_unreported_3247_ = lean_ctor_get(v_log_3246_, 1);
v___x_3248_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3247_);
if (v___x_3248_ == 0)
{
uint8_t v___x_3249_; 
v___x_3249_ = 1;
return v___x_3249_;
}
else
{
uint8_t v___x_3250_; 
v___x_3250_ = 0;
return v___x_3250_;
}
}
}
LEAN_EXPORT void l_Lean_MessageLog_hasUnreported_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_3246_ = stack[0].m_obj;
uint8_t v_res_3251_;
v_res_3251_ = l_Lean_MessageLog_hasUnreported(v_log_3246_);
stack->m_num = v_res_3251_;
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3252_){
_start:
{
uint8_t v_res_3253_; lean_object* v_r_3254_; 
v_res_3253_ = l_Lean_MessageLog_hasUnreported(v_log_3252_);
lean_dec_ref(v_log_3252_);
v_r_3254_ = lean_box(v_res_3253_);
return v_r_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3255_, lean_object* v_log_3256_){
_start:
{
lean_object* v_reported_3257_; lean_object* v_unreported_3258_; lean_object* v_loggedKinds_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3267_; 
v_reported_3257_ = lean_ctor_get(v_log_3256_, 0);
v_unreported_3258_ = lean_ctor_get(v_log_3256_, 1);
v_loggedKinds_3259_ = lean_ctor_get(v_log_3256_, 2);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_log_3256_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3261_ = v_log_3256_;
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_loggedKinds_3259_);
lean_inc(v_unreported_3258_);
lean_inc(v_reported_3257_);
lean_dec(v_log_3256_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3267_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3263_ = l_Lean_PersistentArray_push___redArg(v_unreported_3258_, v_msg_3255_);
if (v_isShared_3262_ == 0)
{
lean_ctor_set(v___x_3261_, 1, v___x_3263_);
v___x_3265_ = v___x_3261_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_reported_3257_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_loggedKinds_3259_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3270_, lean_object* v_x_3271_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_b_u2082_3270_);
return v___x_3272_;
}
else
{
lean_object* v___x_3273_; 
v___x_3273_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3274_, lean_object* v_x_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3274_, v_x_3275_);
lean_dec(v_x_3275_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3277_, lean_object* v_k_3278_, lean_object* v_t_3279_){
_start:
{
if (lean_obj_tag(v_t_3279_) == 0)
{
lean_object* v_size_3280_; lean_object* v_k_3281_; lean_object* v_v_3282_; lean_object* v_l_3283_; lean_object* v_r_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3299_; 
v_size_3280_ = lean_ctor_get(v_t_3279_, 0);
v_k_3281_ = lean_ctor_get(v_t_3279_, 1);
v_v_3282_ = lean_ctor_get(v_t_3279_, 2);
v_l_3283_ = lean_ctor_get(v_t_3279_, 3);
v_r_3284_ = lean_ctor_get(v_t_3279_, 4);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_t_3279_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3286_ = v_t_3279_;
v_isShared_3287_ = v_isSharedCheck_3299_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_r_3284_);
lean_inc(v_l_3283_);
lean_inc(v_v_3282_);
lean_inc(v_k_3281_);
lean_inc(v_size_3280_);
lean_dec(v_t_3279_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3299_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
uint8_t v___x_3288_; 
v___x_3288_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3278_, v_k_3281_);
switch(v___x_3288_)
{
case 0:
{
lean_object* v_impl_3289_; lean_object* v___x_3290_; 
lean_del_object(v___x_3286_);
lean_dec(v_size_3280_);
v_impl_3289_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3277_, v_k_3278_, v_l_3283_);
v___x_3290_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3281_, v_v_3282_, v_impl_3289_, v_r_3284_);
return v___x_3290_;
}
case 1:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v_val_3293_; lean_object* v___x_3295_; 
lean_dec(v_k_3281_);
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v_v_3282_);
v___x_3292_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3277_, v___x_3291_);
lean_dec_ref_known(v___x_3291_, 1);
v_val_3293_ = lean_ctor_get(v___x_3292_, 0);
lean_inc(v_val_3293_);
lean_dec(v___x_3292_);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 2, v_val_3293_);
lean_ctor_set(v___x_3286_, 1, v_k_3278_);
v___x_3295_ = v___x_3286_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_size_3280_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_k_3278_);
lean_ctor_set(v_reuseFailAlloc_3296_, 2, v_val_3293_);
lean_ctor_set(v_reuseFailAlloc_3296_, 3, v_l_3283_);
lean_ctor_set(v_reuseFailAlloc_3296_, 4, v_r_3284_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
default: 
{
lean_object* v_impl_3297_; lean_object* v___x_3298_; 
lean_del_object(v___x_3286_);
lean_dec(v_size_3280_);
v_impl_3297_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3277_, v_k_3278_, v_r_3284_);
v___x_3298_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3281_, v_v_3282_, v_l_3283_, v_impl_3297_);
return v___x_3298_;
}
}
}
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_val_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3277_, v___x_3300_);
v_val_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_val_3302_);
lean_dec(v___x_3301_);
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v_k_3278_);
lean_ctor_set(v___x_3304_, 2, v_val_3302_);
lean_ctor_set(v___x_3304_, 3, v_t_3279_);
lean_ctor_set(v___x_3304_, 4, v_t_3279_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3305_, lean_object* v_x_3306_){
_start:
{
if (lean_obj_tag(v_x_3306_) == 0)
{
lean_object* v_k_3307_; lean_object* v_v_3308_; lean_object* v_l_3309_; lean_object* v_r_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_k_3307_ = lean_ctor_get(v_x_3306_, 1);
lean_inc(v_k_3307_);
v_v_3308_ = lean_ctor_get(v_x_3306_, 2);
lean_inc(v_v_3308_);
v_l_3309_ = lean_ctor_get(v_x_3306_, 3);
lean_inc(v_l_3309_);
v_r_3310_ = lean_ctor_get(v_x_3306_, 4);
lean_inc(v_r_3310_);
lean_dec_ref_known(v_x_3306_, 5);
v___x_3311_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3305_, v_l_3309_);
v___x_3312_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3308_, v_k_3307_, v___x_3311_);
v_init_3305_ = v___x_3312_;
v_x_3306_ = v_r_3310_;
goto _start;
}
else
{
return v_init_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3314_, lean_object* v_l_u2082_3315_){
_start:
{
lean_object* v_reported_3316_; lean_object* v_unreported_3317_; lean_object* v_loggedKinds_3318_; lean_object* v_reported_3319_; lean_object* v_unreported_3320_; lean_object* v_loggedKinds_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3331_; 
v_reported_3316_ = lean_ctor_get(v_l_u2081_3314_, 0);
lean_inc_ref(v_reported_3316_);
v_unreported_3317_ = lean_ctor_get(v_l_u2081_3314_, 1);
lean_inc_ref(v_unreported_3317_);
v_loggedKinds_3318_ = lean_ctor_get(v_l_u2081_3314_, 2);
lean_inc(v_loggedKinds_3318_);
lean_dec_ref(v_l_u2081_3314_);
v_reported_3319_ = lean_ctor_get(v_l_u2082_3315_, 0);
v_unreported_3320_ = lean_ctor_get(v_l_u2082_3315_, 1);
v_loggedKinds_3321_ = lean_ctor_get(v_l_u2082_3315_, 2);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_l_u2082_3315_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3323_ = v_l_u2082_3315_;
v_isShared_3324_ = v_isSharedCheck_3331_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_loggedKinds_3321_);
lean_inc(v_unreported_3320_);
lean_inc(v_reported_3319_);
lean_dec(v_l_u2082_3315_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3331_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3325_ = l_Lean_PersistentArray_append___redArg(v_reported_3316_, v_reported_3319_);
lean_dec_ref(v_reported_3319_);
v___x_3326_ = l_Lean_PersistentArray_append___redArg(v_unreported_3317_, v_unreported_3320_);
lean_dec_ref(v_unreported_3320_);
v___x_3327_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3318_, v_loggedKinds_3321_);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 2, v___x_3327_);
lean_ctor_set(v___x_3323_, 1, v___x_3326_);
lean_ctor_set(v___x_3323_, 0, v___x_3325_);
v___x_3329_ = v___x_3323_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3332_, lean_object* v_k_3333_, lean_object* v_t_3334_, lean_object* v_hl_3335_){
_start:
{
lean_object* v___x_3336_; 
v___x_3336_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3332_, v_k_3333_, v_t_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3337_, lean_object* v_t_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3337_, v_t_3338_);
return v___x_3339_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3342_, size_t v_i_3343_, size_t v_stop_3344_){
_start:
{
uint8_t v___x_3345_; 
v___x_3345_ = lean_usize_dec_eq(v_i_3343_, v_stop_3344_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; uint8_t v_severity_3347_; 
v___x_3346_ = lean_array_uget_borrowed(v_as_3342_, v_i_3343_);
v_severity_3347_ = lean_ctor_get_uint8(v___x_3346_, sizeof(void*)*5 + 1);
if (v_severity_3347_ == 2)
{
uint8_t v___x_3348_; 
v___x_3348_ = 1;
return v___x_3348_;
}
else
{
size_t v___x_3349_; size_t v___x_3350_; 
v___x_3349_ = ((size_t)1ULL);
v___x_3350_ = lean_usize_add(v_i_3343_, v___x_3349_);
v_i_3343_ = v___x_3350_;
goto _start;
}
}
else
{
uint8_t v___x_3352_; 
v___x_3352_ = 0;
return v___x_3352_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3342_ = stack[0].m_obj;
size_t v_i_3343_ = stack[1].m_num;
size_t v_stop_3344_ = stack[2].m_num;
uint8_t v_res_3353_;
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3342_, v_i_3343_, v_stop_3344_);
stack->m_num = v_res_3353_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3354_, lean_object* v_i_3355_, lean_object* v_stop_3356_){
_start:
{
size_t v_i_boxed_3357_; size_t v_stop_boxed_3358_; uint8_t v_res_3359_; lean_object* v_r_3360_; 
v_i_boxed_3357_ = lean_unbox_usize(v_i_3355_);
lean_dec(v_i_3355_);
v_stop_boxed_3358_ = lean_unbox_usize(v_stop_3356_);
lean_dec(v_stop_3356_);
v_res_3359_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3354_, v_i_boxed_3357_, v_stop_boxed_3358_);
lean_dec_ref(v_as_3354_);
v_r_3360_ = lean_box(v_res_3359_);
return v_r_3360_;
}
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3361_){
_start:
{
if (lean_obj_tag(v_x_3361_) == 0)
{
lean_object* v_cs_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_cs_3362_ = lean_ctor_get(v_x_3361_, 0);
v___x_3363_ = lean_unsigned_to_nat(0u);
v___x_3364_ = lean_array_get_size(v_cs_3362_);
v___x_3365_ = lean_nat_dec_lt(v___x_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
return v___x_3365_;
}
else
{
if (v___x_3365_ == 0)
{
return v___x_3365_;
}
else
{
size_t v___x_3366_; size_t v___x_3367_; uint8_t v___x_3368_; 
v___x_3366_ = ((size_t)0ULL);
v___x_3367_ = lean_usize_of_nat(v___x_3364_);
v___x_3368_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3362_, v___x_3366_, v___x_3367_);
return v___x_3368_;
}
}
}
else
{
lean_object* v_vs_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v_vs_3369_ = lean_ctor_get(v_x_3361_, 0);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_array_get_size(v_vs_3369_);
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
v___x_3375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3369_, v___x_3373_, v___x_3374_);
return v___x_3375_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3361_ = stack[0].m_obj;
uint8_t v_res_3376_;
v_res_3376_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3361_);
stack->m_num = v_res_3376_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3377_, size_t v_i_3378_, size_t v_stop_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_eq(v_i_3378_, v_stop_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = lean_array_uget_borrowed(v_as_3377_, v_i_3378_);
v___x_3382_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3381_);
if (v___x_3382_ == 0)
{
size_t v___x_3383_; size_t v___x_3384_; 
v___x_3383_ = ((size_t)1ULL);
v___x_3384_ = lean_usize_add(v_i_3378_, v___x_3383_);
v_i_3378_ = v___x_3384_;
goto _start;
}
else
{
return v___x_3382_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3377_ = stack[0].m_obj;
size_t v_i_3378_ = stack[1].m_num;
size_t v_stop_3379_ = stack[2].m_num;
uint8_t v_res_3387_;
v_res_3387_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3377_, v_i_3378_, v_stop_3379_);
stack->m_num = v_res_3387_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3388_, lean_object* v_i_3389_, lean_object* v_stop_3390_){
_start:
{
size_t v_i_boxed_3391_; size_t v_stop_boxed_3392_; uint8_t v_res_3393_; lean_object* v_r_3394_; 
v_i_boxed_3391_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_stop_boxed_3392_ = lean_unbox_usize(v_stop_3390_);
lean_dec(v_stop_3390_);
v_res_3393_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3388_, v_i_boxed_3391_, v_stop_boxed_3392_);
lean_dec_ref(v_as_3388_);
v_r_3394_ = lean_box(v_res_3393_);
return v_r_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3395_){
_start:
{
uint8_t v_res_3396_; lean_object* v_r_3397_; 
v_res_3396_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3395_);
lean_dec_ref(v_x_3395_);
v_r_3397_ = lean_box(v_res_3396_);
return v_r_3397_;
}
}
uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3398_){
_start:
{
lean_object* v_root_3399_; lean_object* v_tail_3400_; uint8_t v___x_3401_; 
v_root_3399_ = lean_ctor_get(v_t_3398_, 0);
v_tail_3400_ = lean_ctor_get(v_t_3398_, 1);
v___x_3401_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = lean_unsigned_to_nat(0u);
v___x_3403_ = lean_array_get_size(v_tail_3400_);
v___x_3404_ = lean_nat_dec_lt(v___x_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
return v___x_3404_;
}
else
{
if (v___x_3404_ == 0)
{
return v___x_3404_;
}
else
{
size_t v___x_3405_; size_t v___x_3406_; uint8_t v___x_3407_; 
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = lean_usize_of_nat(v___x_3403_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3400_, v___x_3405_, v___x_3406_);
return v___x_3407_;
}
}
}
else
{
return v___x_3401_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3398_ = stack[0].m_obj;
uint8_t v_res_3408_;
v_res_3408_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3398_);
stack->m_num = v_res_3408_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3409_){
_start:
{
uint8_t v_res_3410_; lean_object* v_r_3411_; 
v_res_3410_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3409_);
lean_dec_ref(v_t_3409_);
v_r_3411_ = lean_box(v_res_3410_);
return v_r_3411_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3412_, lean_object* v_as_3413_, size_t v_i_3414_, size_t v_stop_3415_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_eq(v_i_3414_, v_stop_3415_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; uint8_t v_severity_3418_; uint8_t v___x_3419_; 
v___x_3417_ = lean_array_uget_borrowed(v_as_3413_, v_i_3414_);
v_severity_3418_ = lean_ctor_get_uint8(v___x_3417_, sizeof(void*)*5 + 1);
v___x_3419_ = 1;
if (v_severity_3418_ == 2)
{
return v___x_3419_;
}
else
{
if (v___x_3412_ == 0)
{
size_t v___x_3420_; size_t v___x_3421_; 
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3414_, v___x_3420_);
v_i_3414_ = v___x_3421_;
goto _start;
}
else
{
return v___x_3419_;
}
}
}
else
{
uint8_t v___x_3423_; 
v___x_3423_ = 0;
return v___x_3423_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3412_ = stack[0].m_num;
lean_object* v_as_3413_ = stack[1].m_obj;
size_t v_i_3414_ = stack[2].m_num;
size_t v_stop_3415_ = stack[3].m_num;
uint8_t v_res_3424_;
v_res_3424_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3412_, v_as_3413_, v_i_3414_, v_stop_3415_);
stack->m_num = v_res_3424_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3425_, lean_object* v_as_3426_, lean_object* v_i_3427_, lean_object* v_stop_3428_){
_start:
{
uint8_t v___x_1846__boxed_3429_; size_t v_i_boxed_3430_; size_t v_stop_boxed_3431_; uint8_t v_res_3432_; lean_object* v_r_3433_; 
v___x_1846__boxed_3429_ = lean_unbox(v___x_3425_);
v_i_boxed_3430_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_stop_boxed_3431_ = lean_unbox_usize(v_stop_3428_);
lean_dec(v_stop_3428_);
v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1846__boxed_3429_, v_as_3426_, v_i_boxed_3430_, v_stop_boxed_3431_);
lean_dec_ref(v_as_3426_);
v_r_3433_ = lean_box(v_res_3432_);
return v_r_3433_;
}
}
uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3434_, lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
lean_object* v_cs_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; 
v_cs_3436_ = lean_ctor_get(v_x_3435_, 0);
v___x_3437_ = lean_unsigned_to_nat(0u);
v___x_3438_ = lean_array_get_size(v_cs_3436_);
v___x_3439_ = lean_nat_dec_lt(v___x_3437_, v___x_3438_);
if (v___x_3439_ == 0)
{
return v___x_3439_;
}
else
{
if (v___x_3439_ == 0)
{
return v___x_3439_;
}
else
{
size_t v___x_3440_; size_t v___x_3441_; uint8_t v___x_3442_; 
v___x_3440_ = ((size_t)0ULL);
v___x_3441_ = lean_usize_of_nat(v___x_3438_);
v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3434_, v_cs_3436_, v___x_3440_, v___x_3441_);
return v___x_3442_;
}
}
}
else
{
lean_object* v_vs_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_vs_3443_ = lean_ctor_get(v_x_3435_, 0);
v___x_3444_ = lean_unsigned_to_nat(0u);
v___x_3445_ = lean_array_get_size(v_vs_3443_);
v___x_3446_ = lean_nat_dec_lt(v___x_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
return v___x_3446_;
}
else
{
if (v___x_3446_ == 0)
{
return v___x_3446_;
}
else
{
size_t v___x_3447_; size_t v___x_3448_; uint8_t v___x_3449_; 
v___x_3447_ = ((size_t)0ULL);
v___x_3448_ = lean_usize_of_nat(v___x_3445_);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3434_, v_vs_3443_, v___x_3447_, v___x_3448_);
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3434_ = stack[0].m_num;
lean_object* v_x_3435_ = stack[1].m_obj;
uint8_t v_res_3450_;
v_res_3450_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3434_, v_x_3435_);
stack->m_num = v_res_3450_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3451_, lean_object* v_as_3452_, size_t v_i_3453_, size_t v_stop_3454_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_eq(v_i_3453_, v_stop_3454_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = lean_array_uget_borrowed(v_as_3452_, v_i_3453_);
v___x_3457_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3451_, v___x_3456_);
if (v___x_3457_ == 0)
{
size_t v___x_3458_; size_t v___x_3459_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3453_, v___x_3458_);
v_i_3453_ = v___x_3459_;
goto _start;
}
else
{
return v___x_3457_;
}
}
else
{
uint8_t v___x_3461_; 
v___x_3461_ = 0;
return v___x_3461_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3451_ = stack[0].m_num;
lean_object* v_as_3452_ = stack[1].m_obj;
size_t v_i_3453_ = stack[2].m_num;
size_t v_stop_3454_ = stack[3].m_num;
uint8_t v_res_3462_;
v_res_3462_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3451_, v_as_3452_, v_i_3453_, v_stop_3454_);
stack->m_num = v_res_3462_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3463_, lean_object* v_as_3464_, lean_object* v_i_3465_, lean_object* v_stop_3466_){
_start:
{
uint8_t v___x_1872__boxed_3467_; size_t v_i_boxed_3468_; size_t v_stop_boxed_3469_; uint8_t v_res_3470_; lean_object* v_r_3471_; 
v___x_1872__boxed_3467_ = lean_unbox(v___x_3463_);
v_i_boxed_3468_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_stop_boxed_3469_ = lean_unbox_usize(v_stop_3466_);
lean_dec(v_stop_3466_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1872__boxed_3467_, v_as_3464_, v_i_boxed_3468_, v_stop_boxed_3469_);
lean_dec_ref(v_as_3464_);
v_r_3471_ = lean_box(v_res_3470_);
return v_r_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3472_, lean_object* v_x_3473_){
_start:
{
uint8_t v___x_1880__boxed_3474_; uint8_t v_res_3475_; lean_object* v_r_3476_; 
v___x_1880__boxed_3474_ = lean_unbox(v___x_3472_);
v_res_3475_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1880__boxed_3474_, v_x_3473_);
lean_dec_ref(v_x_3473_);
v_r_3476_ = lean_box(v_res_3475_);
return v_r_3476_;
}
}
uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3477_, lean_object* v_t_3478_){
_start:
{
lean_object* v_root_3479_; lean_object* v_tail_3480_; uint8_t v___x_3481_; 
v_root_3479_ = lean_ctor_get(v_t_3478_, 0);
v_tail_3480_ = lean_ctor_get(v_t_3478_, 1);
v___x_3481_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3477_, v_root_3479_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_array_get_size(v_tail_3480_);
v___x_3484_ = lean_nat_dec_lt(v___x_3482_, v___x_3483_);
if (v___x_3484_ == 0)
{
return v___x_3484_;
}
else
{
if (v___x_3484_ == 0)
{
return v___x_3484_;
}
else
{
size_t v___x_3485_; size_t v___x_3486_; uint8_t v___x_3487_; 
v___x_3485_ = ((size_t)0ULL);
v___x_3486_ = lean_usize_of_nat(v___x_3483_);
v___x_3487_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3477_, v_tail_3480_, v___x_3485_, v___x_3486_);
return v___x_3487_;
}
}
}
else
{
return v___x_3481_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3477_ = stack[0].m_num;
lean_object* v_t_3478_ = stack[1].m_obj;
uint8_t v_res_3488_;
v_res_3488_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3477_, v_t_3478_);
stack->m_num = v_res_3488_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3489_, lean_object* v_t_3490_){
_start:
{
uint8_t v___x_1950__boxed_3491_; uint8_t v_res_3492_; lean_object* v_r_3493_; 
v___x_1950__boxed_3491_ = lean_unbox(v___x_3489_);
v_res_3492_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1950__boxed_3491_, v_t_3490_);
lean_dec_ref(v_t_3490_);
v_r_3493_ = lean_box(v_res_3492_);
return v_r_3493_;
}
}
uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3494_){
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
LEAN_EXPORT void l_Lean_MessageLog_hasErrors_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_3494_ = stack[0].m_obj;
uint8_t v_res_3499_;
v_res_3499_ = l_Lean_MessageLog_hasErrors(v_log_3494_);
stack->m_num = v_res_3499_;
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3500_){
_start:
{
uint8_t v_res_3501_; lean_object* v_r_3502_; 
v_res_3501_ = l_Lean_MessageLog_hasErrors(v_log_3500_);
lean_dec_ref(v_log_3500_);
v_r_3502_ = lean_box(v_res_3501_);
return v_r_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3503_){
_start:
{
lean_object* v_reported_3504_; lean_object* v_unreported_3505_; lean_object* v_loggedKinds_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3517_; 
v_reported_3504_ = lean_ctor_get(v_log_3503_, 0);
v_unreported_3505_ = lean_ctor_get(v_log_3503_, 1);
v_loggedKinds_3506_ = lean_ctor_get(v_log_3503_, 2);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_log_3503_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3508_ = v_log_3503_;
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_loggedKinds_3506_);
lean_inc(v_unreported_3505_);
lean_inc(v_reported_3504_);
lean_dec(v_log_3503_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3517_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3510_ = l_Lean_PersistentArray_append___redArg(v_reported_3504_, v_unreported_3505_);
lean_dec_ref(v_unreported_3505_);
v___x_3511_ = lean_unsigned_to_nat(32u);
v___x_3512_ = lean_mk_empty_array_with_capacity(v___x_3511_);
lean_dec_ref(v___x_3512_);
v___x_3513_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v___x_3513_);
lean_ctor_set(v___x_3508_, 0, v___x_3510_);
v___x_3515_ = v___x_3508_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3510_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3516_, 2, v_loggedKinds_3506_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3518_, size_t v_i_3519_, lean_object* v_bs_3520_){
_start:
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_usize_dec_lt(v_i_3519_, v_sz_3518_);
if (v___x_3521_ == 0)
{
return v_bs_3520_;
}
else
{
lean_object* v_v_3522_; lean_object* v_fileName_3523_; lean_object* v_pos_3524_; lean_object* v_endPos_3525_; uint8_t v_keepFullRange_3526_; uint8_t v_severity_3527_; uint8_t v_isSilent_3528_; lean_object* v_caption_3529_; lean_object* v_data_3530_; lean_object* v___x_3531_; lean_object* v_bs_x27_3532_; lean_object* v___y_3534_; 
v_v_3522_ = lean_array_uget(v_bs_3520_, v_i_3519_);
v_fileName_3523_ = lean_ctor_get(v_v_3522_, 0);
v_pos_3524_ = lean_ctor_get(v_v_3522_, 1);
v_endPos_3525_ = lean_ctor_get(v_v_3522_, 2);
v_keepFullRange_3526_ = lean_ctor_get_uint8(v_v_3522_, sizeof(void*)*5);
v_severity_3527_ = lean_ctor_get_uint8(v_v_3522_, sizeof(void*)*5 + 1);
v_isSilent_3528_ = lean_ctor_get_uint8(v_v_3522_, sizeof(void*)*5 + 2);
v_caption_3529_ = lean_ctor_get(v_v_3522_, 3);
v_data_3530_ = lean_ctor_get(v_v_3522_, 4);
v___x_3531_ = lean_unsigned_to_nat(0u);
v_bs_x27_3532_ = lean_array_uset(v_bs_3520_, v_i_3519_, v___x_3531_);
if (v_severity_3527_ == 2)
{
lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3546_; 
lean_inc(v_data_3530_);
lean_inc_ref(v_caption_3529_);
lean_inc(v_endPos_3525_);
lean_inc_ref(v_pos_3524_);
lean_inc_ref(v_fileName_3523_);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_v_3522_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; lean_object* v_unused_3550_; lean_object* v_unused_3551_; 
v_unused_3547_ = lean_ctor_get(v_v_3522_, 4);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_v_3522_, 3);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_v_3522_, 2);
lean_dec(v_unused_3549_);
v_unused_3550_ = lean_ctor_get(v_v_3522_, 1);
lean_dec(v_unused_3550_);
v_unused_3551_ = lean_ctor_get(v_v_3522_, 0);
lean_dec(v_unused_3551_);
v___x_3540_ = v_v_3522_;
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
else
{
lean_dec(v_v_3522_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3546_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
uint8_t v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = 1;
if (v_isShared_3541_ == 0)
{
v___x_3544_ = v___x_3540_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_fileName_3523_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_pos_3524_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_endPos_3525_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_caption_3529_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v_data_3530_);
lean_ctor_set_uint8(v_reuseFailAlloc_3545_, sizeof(void*)*5, v_keepFullRange_3526_);
lean_ctor_set_uint8(v_reuseFailAlloc_3545_, sizeof(void*)*5 + 2, v_isSilent_3528_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_ctor_set_uint8(v___x_3544_, sizeof(void*)*5 + 1, v___x_3542_);
v___y_3534_ = v___x_3544_;
goto v___jp_3533_;
}
}
}
else
{
v___y_3534_ = v_v_3522_;
goto v___jp_3533_;
}
v___jp_3533_:
{
size_t v___x_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_add(v_i_3519_, v___x_3535_);
v___x_3537_ = lean_array_uset(v_bs_x27_3532_, v_i_3519_, v___y_3534_);
v_i_3519_ = v___x_3536_;
v_bs_3520_ = v___x_3537_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3518_ = stack[0].m_num;
size_t v_i_3519_ = stack[1].m_num;
lean_object* v_bs_3520_ = stack[2].m_obj;
lean_object* v_res_3552_;
v_res_3552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3518_, v_i_3519_, v_bs_3520_);
stack->m_obj
 = v_res_3552_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3553_, lean_object* v_i_3554_, lean_object* v_bs_3555_){
_start:
{
size_t v_sz_boxed_3556_; size_t v_i_boxed_3557_; lean_object* v_res_3558_; 
v_sz_boxed_3556_ = lean_unbox_usize(v_sz_3553_);
lean_dec(v_sz_3553_);
v_i_boxed_3557_ = lean_unbox_usize(v_i_3554_);
lean_dec(v_i_3554_);
v_res_3558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3556_, v_i_boxed_3557_, v_bs_3555_);
return v_res_3558_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3559_, size_t v_i_3560_, lean_object* v_bs_3561_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = lean_usize_dec_lt(v_i_3560_, v_sz_3559_);
if (v___x_3562_ == 0)
{
return v_bs_3561_;
}
else
{
lean_object* v_v_3563_; lean_object* v___x_3564_; lean_object* v_bs_x27_3565_; lean_object* v___x_3566_; size_t v___x_3567_; size_t v___x_3568_; lean_object* v___x_3569_; 
v_v_3563_ = lean_array_uget(v_bs_3561_, v_i_3560_);
v___x_3564_ = lean_unsigned_to_nat(0u);
v_bs_x27_3565_ = lean_array_uset(v_bs_3561_, v_i_3560_, v___x_3564_);
v___x_3566_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3563_);
v___x_3567_ = ((size_t)1ULL);
v___x_3568_ = lean_usize_add(v_i_3560_, v___x_3567_);
v___x_3569_ = lean_array_uset(v_bs_x27_3565_, v_i_3560_, v___x_3566_);
v_i_3560_ = v___x_3568_;
v_bs_3561_ = v___x_3569_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3559_ = stack[0].m_num;
size_t v_i_3560_ = stack[1].m_num;
lean_object* v_bs_3561_ = stack[2].m_obj;
lean_object* v_res_3571_;
v_res_3571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3559_, v_i_3560_, v_bs_3561_);
stack->m_obj
 = v_res_3571_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3572_){
_start:
{
if (lean_obj_tag(v_x_3572_) == 0)
{
lean_object* v_cs_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
v_cs_3573_ = lean_ctor_get(v_x_3572_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3575_ = v_x_3572_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_cs_3573_);
lean_dec(v_x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
size_t v_sz_3577_; size_t v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v_sz_3577_ = lean_array_size(v_cs_3573_);
v___x_3578_ = ((size_t)0ULL);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3577_, v___x_3578_, v_cs_3573_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3579_);
v___x_3581_ = v___x_3575_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
else
{
lean_object* v_vs_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3594_; 
v_vs_3584_ = lean_ctor_get(v_x_3572_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3586_ = v_x_3572_;
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_vs_3584_);
lean_dec(v_x_3572_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3594_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
size_t v_sz_3588_; size_t v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v_sz_3588_ = lean_array_size(v_vs_3584_);
v___x_3589_ = ((size_t)0ULL);
v___x_3590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3588_, v___x_3589_, v_vs_3584_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v___x_3590_);
v___x_3592_ = v___x_3586_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3595_, lean_object* v_i_3596_, lean_object* v_bs_3597_){
_start:
{
size_t v_sz_boxed_3598_; size_t v_i_boxed_3599_; lean_object* v_res_3600_; 
v_sz_boxed_3598_ = lean_unbox_usize(v_sz_3595_);
lean_dec(v_sz_3595_);
v_i_boxed_3599_ = lean_unbox_usize(v_i_3596_);
lean_dec(v_i_3596_);
v_res_3600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3598_, v_i_boxed_3599_, v_bs_3597_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3601_){
_start:
{
lean_object* v_root_3602_; lean_object* v_tail_3603_; lean_object* v_size_3604_; size_t v_shift_3605_; lean_object* v_tailOff_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3617_; 
v_root_3602_ = lean_ctor_get(v_t_3601_, 0);
v_tail_3603_ = lean_ctor_get(v_t_3601_, 1);
v_size_3604_ = lean_ctor_get(v_t_3601_, 2);
v_shift_3605_ = lean_ctor_get_usize(v_t_3601_, 4);
v_tailOff_3606_ = lean_ctor_get(v_t_3601_, 3);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_t_3601_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3608_ = v_t_3601_;
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_tailOff_3606_);
lean_inc(v_size_3604_);
lean_inc(v_tail_3603_);
lean_inc(v_root_3602_);
lean_dec(v_t_3601_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3617_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; size_t v_sz_3611_; size_t v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3615_; 
v___x_3610_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3602_);
v_sz_3611_ = lean_array_size(v_tail_3603_);
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3611_, v___x_3612_, v_tail_3603_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 1, v___x_3613_);
lean_ctor_set(v___x_3608_, 0, v___x_3610_);
v___x_3615_ = v___x_3608_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v_size_3604_);
lean_ctor_set(v_reuseFailAlloc_3616_, 3, v_tailOff_3606_);
lean_ctor_set_usize(v_reuseFailAlloc_3616_, 4, v_shift_3605_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3618_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v_unreported_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3631_; 
v___x_3619_ = lean_unsigned_to_nat(32u);
v___x_3620_ = lean_mk_empty_array_with_capacity(v___x_3619_);
lean_dec_ref(v___x_3620_);
v___x_3621_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3622_ = lean_ctor_get(v_log_3618_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_log_3618_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; lean_object* v_unused_3633_; 
v_unused_3632_ = lean_ctor_get(v_log_3618_, 2);
lean_dec(v_unused_3632_);
v_unused_3633_ = lean_ctor_get(v_log_3618_, 0);
lean_dec(v_unused_3633_);
v___x_3624_ = v_log_3618_;
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_unreported_3622_);
lean_dec(v_log_3618_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3631_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3626_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3622_);
v___x_3627_ = l_Lean_NameSet_empty;
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 2, v___x_3627_);
lean_ctor_set(v___x_3624_, 1, v___x_3626_);
lean_ctor_set(v___x_3624_, 0, v___x_3621_);
v___x_3629_ = v___x_3624_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3634_, size_t v_i_3635_, lean_object* v_bs_3636_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_usize_dec_lt(v_i_3635_, v_sz_3634_);
if (v___x_3637_ == 0)
{
return v_bs_3636_;
}
else
{
lean_object* v_v_3638_; lean_object* v_fileName_3639_; lean_object* v_pos_3640_; lean_object* v_endPos_3641_; uint8_t v_keepFullRange_3642_; uint8_t v_severity_3643_; uint8_t v_isSilent_3644_; lean_object* v_caption_3645_; lean_object* v_data_3646_; lean_object* v___x_3647_; lean_object* v_bs_x27_3648_; lean_object* v___y_3650_; 
v_v_3638_ = lean_array_uget(v_bs_3636_, v_i_3635_);
v_fileName_3639_ = lean_ctor_get(v_v_3638_, 0);
v_pos_3640_ = lean_ctor_get(v_v_3638_, 1);
v_endPos_3641_ = lean_ctor_get(v_v_3638_, 2);
v_keepFullRange_3642_ = lean_ctor_get_uint8(v_v_3638_, sizeof(void*)*5);
v_severity_3643_ = lean_ctor_get_uint8(v_v_3638_, sizeof(void*)*5 + 1);
v_isSilent_3644_ = lean_ctor_get_uint8(v_v_3638_, sizeof(void*)*5 + 2);
v_caption_3645_ = lean_ctor_get(v_v_3638_, 3);
v_data_3646_ = lean_ctor_get(v_v_3638_, 4);
v___x_3647_ = lean_unsigned_to_nat(0u);
v_bs_x27_3648_ = lean_array_uset(v_bs_3636_, v_i_3635_, v___x_3647_);
if (v_severity_3643_ == 2)
{
lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3662_; 
lean_inc(v_data_3646_);
lean_inc_ref(v_caption_3645_);
lean_inc(v_endPos_3641_);
lean_inc_ref(v_pos_3640_);
lean_inc_ref(v_fileName_3639_);
v_isSharedCheck_3662_ = !lean_is_exclusive(v_v_3638_);
if (v_isSharedCheck_3662_ == 0)
{
lean_object* v_unused_3663_; lean_object* v_unused_3664_; lean_object* v_unused_3665_; lean_object* v_unused_3666_; lean_object* v_unused_3667_; 
v_unused_3663_ = lean_ctor_get(v_v_3638_, 4);
lean_dec(v_unused_3663_);
v_unused_3664_ = lean_ctor_get(v_v_3638_, 3);
lean_dec(v_unused_3664_);
v_unused_3665_ = lean_ctor_get(v_v_3638_, 2);
lean_dec(v_unused_3665_);
v_unused_3666_ = lean_ctor_get(v_v_3638_, 1);
lean_dec(v_unused_3666_);
v_unused_3667_ = lean_ctor_get(v_v_3638_, 0);
lean_dec(v_unused_3667_);
v___x_3656_ = v_v_3638_;
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
else
{
lean_dec(v_v_3638_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3662_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
uint8_t v___x_3658_; lean_object* v___x_3660_; 
v___x_3658_ = 0;
if (v_isShared_3657_ == 0)
{
v___x_3660_ = v___x_3656_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_fileName_3639_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_pos_3640_);
lean_ctor_set(v_reuseFailAlloc_3661_, 2, v_endPos_3641_);
lean_ctor_set(v_reuseFailAlloc_3661_, 3, v_caption_3645_);
lean_ctor_set(v_reuseFailAlloc_3661_, 4, v_data_3646_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, sizeof(void*)*5, v_keepFullRange_3642_);
lean_ctor_set_uint8(v_reuseFailAlloc_3661_, sizeof(void*)*5 + 2, v_isSilent_3644_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_ctor_set_uint8(v___x_3660_, sizeof(void*)*5 + 1, v___x_3658_);
v___y_3650_ = v___x_3660_;
goto v___jp_3649_;
}
}
}
else
{
v___y_3650_ = v_v_3638_;
goto v___jp_3649_;
}
v___jp_3649_:
{
size_t v___x_3651_; size_t v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = ((size_t)1ULL);
v___x_3652_ = lean_usize_add(v_i_3635_, v___x_3651_);
v___x_3653_ = lean_array_uset(v_bs_x27_3648_, v_i_3635_, v___y_3650_);
v_i_3635_ = v___x_3652_;
v_bs_3636_ = v___x_3653_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3634_ = stack[0].m_num;
size_t v_i_3635_ = stack[1].m_num;
lean_object* v_bs_3636_ = stack[2].m_obj;
lean_object* v_res_3668_;
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3634_, v_i_3635_, v_bs_3636_);
stack->m_obj
 = v_res_3668_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3669_, lean_object* v_i_3670_, lean_object* v_bs_3671_){
_start:
{
size_t v_sz_boxed_3672_; size_t v_i_boxed_3673_; lean_object* v_res_3674_; 
v_sz_boxed_3672_ = lean_unbox_usize(v_sz_3669_);
lean_dec(v_sz_3669_);
v_i_boxed_3673_ = lean_unbox_usize(v_i_3670_);
lean_dec(v_i_3670_);
v_res_3674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3672_, v_i_boxed_3673_, v_bs_3671_);
return v_res_3674_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3675_, size_t v_i_3676_, lean_object* v_bs_3677_){
_start:
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_usize_dec_lt(v_i_3676_, v_sz_3675_);
if (v___x_3678_ == 0)
{
return v_bs_3677_;
}
else
{
lean_object* v_v_3679_; lean_object* v___x_3680_; lean_object* v_bs_x27_3681_; lean_object* v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v_v_3679_ = lean_array_uget(v_bs_3677_, v_i_3676_);
v___x_3680_ = lean_unsigned_to_nat(0u);
v_bs_x27_3681_ = lean_array_uset(v_bs_3677_, v_i_3676_, v___x_3680_);
v___x_3682_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3679_);
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_add(v_i_3676_, v___x_3683_);
v___x_3685_ = lean_array_uset(v_bs_x27_3681_, v_i_3676_, v___x_3682_);
v_i_3676_ = v___x_3684_;
v_bs_3677_ = v___x_3685_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3675_ = stack[0].m_num;
size_t v_i_3676_ = stack[1].m_num;
lean_object* v_bs_3677_ = stack[2].m_obj;
lean_object* v_res_3687_;
v_res_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3675_, v_i_3676_, v_bs_3677_);
stack->m_obj
 = v_res_3687_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3688_){
_start:
{
if (lean_obj_tag(v_x_3688_) == 0)
{
lean_object* v_cs_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3699_; 
v_cs_3689_ = lean_ctor_get(v_x_3688_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3691_ = v_x_3688_;
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_cs_3689_);
lean_dec(v_x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3699_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
size_t v_sz_3693_; size_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
v_sz_3693_ = lean_array_size(v_cs_3689_);
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3693_, v___x_3694_, v_cs_3689_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3695_);
v___x_3697_ = v___x_3691_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
else
{
lean_object* v_vs_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3710_; 
v_vs_3700_ = lean_ctor_get(v_x_3688_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_x_3688_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3702_ = v_x_3688_;
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_vs_3700_);
lean_dec(v_x_3688_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3710_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
size_t v_sz_3704_; size_t v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3708_; 
v_sz_3704_ = lean_array_size(v_vs_3700_);
v___x_3705_ = ((size_t)0ULL);
v___x_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3704_, v___x_3705_, v_vs_3700_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3706_);
v___x_3708_ = v___x_3702_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_bs_3713_){
_start:
{
size_t v_sz_boxed_3714_; size_t v_i_boxed_3715_; lean_object* v_res_3716_; 
v_sz_boxed_3714_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3715_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3714_, v_i_boxed_3715_, v_bs_3713_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3717_){
_start:
{
lean_object* v_root_3718_; lean_object* v_tail_3719_; lean_object* v_size_3720_; size_t v_shift_3721_; lean_object* v_tailOff_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3733_; 
v_root_3718_ = lean_ctor_get(v_t_3717_, 0);
v_tail_3719_ = lean_ctor_get(v_t_3717_, 1);
v_size_3720_ = lean_ctor_get(v_t_3717_, 2);
v_shift_3721_ = lean_ctor_get_usize(v_t_3717_, 4);
v_tailOff_3722_ = lean_ctor_get(v_t_3717_, 3);
v_isSharedCheck_3733_ = !lean_is_exclusive(v_t_3717_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3724_ = v_t_3717_;
v_isShared_3725_ = v_isSharedCheck_3733_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_tailOff_3722_);
lean_inc(v_size_3720_);
lean_inc(v_tail_3719_);
lean_inc(v_root_3718_);
lean_dec(v_t_3717_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3733_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3726_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3718_);
v_sz_3727_ = lean_array_size(v_tail_3719_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3727_, v___x_3728_, v_tail_3719_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 1, v___x_3729_);
lean_ctor_set(v___x_3724_, 0, v___x_3726_);
v___x_3731_ = v___x_3724_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_size_3720_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v_tailOff_3722_);
lean_ctor_set_usize(v_reuseFailAlloc_3732_, 4, v_shift_3721_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3734_){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v_unreported_3738_; lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3747_; 
v___x_3735_ = lean_unsigned_to_nat(32u);
v___x_3736_ = lean_mk_empty_array_with_capacity(v___x_3735_);
lean_dec_ref(v___x_3736_);
v___x_3737_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3738_ = lean_ctor_get(v_log_3734_, 1);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_log_3734_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3748_ = lean_ctor_get(v_log_3734_, 2);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_log_3734_, 0);
lean_dec(v_unused_3749_);
v___x_3740_ = v_log_3734_;
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
else
{
lean_inc(v_unreported_3738_);
lean_dec(v_log_3734_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3747_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
v___x_3742_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3738_);
v___x_3743_ = l_Lean_NameSet_empty;
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 2, v___x_3743_);
lean_ctor_set(v___x_3740_, 1, v___x_3742_);
lean_ctor_set(v___x_3740_, 0, v___x_3737_);
v___x_3745_ = v___x_3740_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v___x_3742_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3750_, size_t v_i_3751_, size_t v_stop_3752_, lean_object* v_b_3753_){
_start:
{
lean_object* v___y_3755_; uint8_t v___x_3759_; 
v___x_3759_ = lean_usize_dec_eq(v_i_3751_, v_stop_3752_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; uint8_t v_severity_3761_; 
v___x_3760_ = lean_array_uget_borrowed(v_as_3750_, v_i_3751_);
v_severity_3761_ = lean_ctor_get_uint8(v___x_3760_, sizeof(void*)*5 + 1);
if (v_severity_3761_ == 0)
{
lean_object* v___x_3762_; 
lean_inc(v___x_3760_);
v___x_3762_ = l_Lean_PersistentArray_push___redArg(v_b_3753_, v___x_3760_);
v___y_3755_ = v___x_3762_;
goto v___jp_3754_;
}
else
{
v___y_3755_ = v_b_3753_;
goto v___jp_3754_;
}
}
else
{
return v_b_3753_;
}
v___jp_3754_:
{
size_t v___x_3756_; size_t v___x_3757_; 
v___x_3756_ = ((size_t)1ULL);
v___x_3757_ = lean_usize_add(v_i_3751_, v___x_3756_);
v_i_3751_ = v___x_3757_;
v_b_3753_ = v___y_3755_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3750_ = stack[0].m_obj;
size_t v_i_3751_ = stack[1].m_num;
size_t v_stop_3752_ = stack[2].m_num;
lean_object* v_b_3753_ = stack[3].m_obj;
lean_object* v_res_3763_;
v_res_3763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3750_, v_i_3751_, v_stop_3752_, v_b_3753_);
stack->m_obj
 = v_res_3763_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3764_, lean_object* v_i_3765_, lean_object* v_stop_3766_, lean_object* v_b_3767_){
_start:
{
size_t v_i_boxed_3768_; size_t v_stop_boxed_3769_; lean_object* v_res_3770_; 
v_i_boxed_3768_ = lean_unbox_usize(v_i_3765_);
lean_dec(v_i_3765_);
v_stop_boxed_3769_ = lean_unbox_usize(v_stop_3766_);
lean_dec(v_stop_3766_);
v_res_3770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3764_, v_i_boxed_3768_, v_stop_boxed_3769_, v_b_3767_);
lean_dec_ref(v_as_3764_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
if (lean_obj_tag(v_x_3771_) == 0)
{
lean_object* v_cs_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_cs_3773_ = lean_ctor_get(v_x_3771_, 0);
v___x_3774_ = lean_unsigned_to_nat(0u);
v___x_3775_ = lean_array_get_size(v_cs_3773_);
v___x_3776_ = lean_nat_dec_lt(v___x_3774_, v___x_3775_);
if (v___x_3776_ == 0)
{
return v_x_3772_;
}
else
{
size_t v___x_3777_; size_t v___x_3778_; lean_object* v___x_3779_; 
v___x_3777_ = ((size_t)0ULL);
v___x_3778_ = lean_usize_of_nat(v___x_3775_);
v___x_3779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3773_, v___x_3777_, v___x_3778_, v_x_3772_);
return v___x_3779_;
}
}
else
{
lean_object* v_vs_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_vs_3780_ = lean_ctor_get(v_x_3771_, 0);
v___x_3781_ = lean_unsigned_to_nat(0u);
v___x_3782_ = lean_array_get_size(v_vs_3780_);
v___x_3783_ = lean_nat_dec_lt(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
return v_x_3772_;
}
else
{
size_t v___x_3784_; size_t v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = ((size_t)0ULL);
v___x_3785_ = lean_usize_of_nat(v___x_3782_);
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3780_, v___x_3784_, v___x_3785_, v_x_3772_);
return v___x_3786_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3787_, size_t v_i_3788_, size_t v_stop_3789_, lean_object* v_b_3790_){
_start:
{
uint8_t v___x_3791_; 
v___x_3791_ = lean_usize_dec_eq(v_i_3788_, v_stop_3789_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; size_t v___x_3794_; size_t v___x_3795_; 
v___x_3792_ = lean_array_uget_borrowed(v_as_3787_, v_i_3788_);
v___x_3793_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3792_, v_b_3790_);
v___x_3794_ = ((size_t)1ULL);
v___x_3795_ = lean_usize_add(v_i_3788_, v___x_3794_);
v_i_3788_ = v___x_3795_;
v_b_3790_ = v___x_3793_;
goto _start;
}
else
{
return v_b_3790_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3787_ = stack[0].m_obj;
size_t v_i_3788_ = stack[1].m_num;
size_t v_stop_3789_ = stack[2].m_num;
lean_object* v_b_3790_ = stack[3].m_obj;
lean_object* v_res_3797_;
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3787_, v_i_3788_, v_stop_3789_, v_b_3790_);
stack->m_obj
 = v_res_3797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3798_, lean_object* v_i_3799_, lean_object* v_stop_3800_, lean_object* v_b_3801_){
_start:
{
size_t v_i_boxed_3802_; size_t v_stop_boxed_3803_; lean_object* v_res_3804_; 
v_i_boxed_3802_ = lean_unbox_usize(v_i_3799_);
lean_dec(v_i_3799_);
v_stop_boxed_3803_ = lean_unbox_usize(v_stop_3800_);
lean_dec(v_stop_3800_);
v_res_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3798_, v_i_boxed_3802_, v_stop_boxed_3803_, v_b_3801_);
lean_dec_ref(v_as_3798_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3805_, lean_object* v_x_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3805_, v_x_3806_);
lean_dec_ref(v_x_3805_);
return v_res_3807_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3808_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3809_, size_t v_x_3810_, size_t v_x_3811_, lean_object* v_x_3812_){
_start:
{
if (lean_obj_tag(v_x_3809_) == 0)
{
lean_object* v_cs_3813_; lean_object* v___x_3814_; size_t v___x_3815_; lean_object* v_j_3816_; lean_object* v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_cs_3813_ = lean_ctor_get(v_x_3809_, 0);
v___x_3814_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3815_ = lean_usize_shift_right(v_x_3810_, v_x_3811_);
v_j_3816_ = lean_usize_to_nat(v___x_3815_);
v___x_3817_ = lean_array_get_borrowed(v___x_3814_, v_cs_3813_, v_j_3816_);
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_shift_left(v___x_3818_, v_x_3811_);
v___x_3820_ = lean_usize_sub(v___x_3819_, v___x_3818_);
v___x_3821_ = lean_usize_land(v_x_3810_, v___x_3820_);
v___x_3822_ = ((size_t)5ULL);
v___x_3823_ = lean_usize_sub(v_x_3811_, v___x_3822_);
v___x_3824_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3817_, v___x_3821_, v___x_3823_, v_x_3812_);
v___x_3825_ = lean_unsigned_to_nat(1u);
v___x_3826_ = lean_nat_add(v_j_3816_, v___x_3825_);
lean_dec(v_j_3816_);
v___x_3827_ = lean_array_get_size(v_cs_3813_);
v___x_3828_ = lean_nat_dec_lt(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_dec(v___x_3826_);
return v___x_3824_;
}
else
{
size_t v___x_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_usize_of_nat(v___x_3826_);
lean_dec(v___x_3826_);
v___x_3830_ = lean_usize_of_nat(v___x_3827_);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3813_, v___x_3829_, v___x_3830_, v___x_3824_);
return v___x_3831_;
}
}
else
{
lean_object* v_vs_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v_vs_3832_ = lean_ctor_get(v_x_3809_, 0);
v___x_3833_ = lean_usize_to_nat(v_x_3810_);
v___x_3834_ = lean_array_get_size(v_vs_3832_);
v___x_3835_ = lean_nat_dec_lt(v___x_3833_, v___x_3834_);
if (v___x_3835_ == 0)
{
lean_dec(v___x_3833_);
return v_x_3812_;
}
else
{
size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; 
v___x_3836_ = lean_usize_of_nat(v___x_3833_);
lean_dec(v___x_3833_);
v___x_3837_ = lean_usize_of_nat(v___x_3834_);
v___x_3838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3832_, v___x_3836_, v___x_3837_, v_x_3812_);
return v___x_3838_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3809_ = stack[0].m_obj;
size_t v_x_3810_ = stack[1].m_num;
size_t v_x_3811_ = stack[2].m_num;
lean_object* v_x_3812_ = stack[3].m_obj;
lean_object* v_res_3839_;
v_res_3839_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3809_, v_x_3810_, v_x_3811_, v_x_3812_);
stack->m_obj
 = v_res_3839_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3840_, lean_object* v_x_3841_, lean_object* v_x_3842_, lean_object* v_x_3843_){
_start:
{
size_t v_x_1185__boxed_3844_; size_t v_x_1186__boxed_3845_; lean_object* v_res_3846_; 
v_x_1185__boxed_3844_ = lean_unbox_usize(v_x_3841_);
lean_dec(v_x_3841_);
v_x_1186__boxed_3845_ = lean_unbox_usize(v_x_3842_);
lean_dec(v_x_3842_);
v_res_3846_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3840_, v_x_1185__boxed_3844_, v_x_1186__boxed_3845_, v_x_3843_);
lean_dec_ref(v_x_3840_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3847_, lean_object* v_init_3848_, lean_object* v_start_3849_){
_start:
{
lean_object* v___x_3850_; uint8_t v___x_3851_; 
v___x_3850_ = lean_unsigned_to_nat(0u);
v___x_3851_ = lean_nat_dec_eq(v_start_3849_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v_root_3852_; lean_object* v_tail_3853_; size_t v_shift_3854_; lean_object* v_tailOff_3855_; uint8_t v___x_3856_; 
v_root_3852_ = lean_ctor_get(v_t_3847_, 0);
v_tail_3853_ = lean_ctor_get(v_t_3847_, 1);
v_shift_3854_ = lean_ctor_get_usize(v_t_3847_, 4);
v_tailOff_3855_ = lean_ctor_get(v_t_3847_, 3);
v___x_3856_ = lean_nat_dec_le(v_tailOff_3855_, v_start_3849_);
if (v___x_3856_ == 0)
{
size_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3857_ = lean_usize_of_nat(v_start_3849_);
v___x_3858_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3852_, v___x_3857_, v_shift_3854_, v_init_3848_);
v___x_3859_ = lean_array_get_size(v_tail_3853_);
v___x_3860_ = lean_nat_dec_lt(v___x_3850_, v___x_3859_);
if (v___x_3860_ == 0)
{
return v___x_3858_;
}
else
{
size_t v___x_3861_; size_t v___x_3862_; lean_object* v___x_3863_; 
v___x_3861_ = ((size_t)0ULL);
v___x_3862_ = lean_usize_of_nat(v___x_3859_);
v___x_3863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3853_, v___x_3861_, v___x_3862_, v___x_3858_);
return v___x_3863_;
}
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3864_ = lean_nat_sub(v_start_3849_, v_tailOff_3855_);
v___x_3865_ = lean_array_get_size(v_tail_3853_);
v___x_3866_ = lean_nat_dec_lt(v___x_3864_, v___x_3865_);
if (v___x_3866_ == 0)
{
lean_dec(v___x_3864_);
return v_init_3848_;
}
else
{
size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = lean_usize_of_nat(v___x_3864_);
lean_dec(v___x_3864_);
v___x_3868_ = lean_usize_of_nat(v___x_3865_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3853_, v___x_3867_, v___x_3868_, v_init_3848_);
return v___x_3869_;
}
}
}
else
{
lean_object* v_root_3870_; lean_object* v_tail_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v_root_3870_ = lean_ctor_get(v_t_3847_, 0);
v_tail_3871_ = lean_ctor_get(v_t_3847_, 1);
v___x_3872_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3870_, v_init_3848_);
v___x_3873_ = lean_array_get_size(v_tail_3871_);
v___x_3874_ = lean_nat_dec_lt(v___x_3850_, v___x_3873_);
if (v___x_3874_ == 0)
{
return v___x_3872_;
}
else
{
size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3875_ = ((size_t)0ULL);
v___x_3876_ = lean_usize_of_nat(v___x_3873_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3871_, v___x_3875_, v___x_3876_, v___x_3872_);
return v___x_3877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3878_, lean_object* v_init_3879_, lean_object* v_start_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3878_, v_init_3879_, v_start_3880_);
lean_dec(v_start_3880_);
lean_dec_ref(v_t_3878_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3882_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v_unreported_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3896_; 
v___x_3883_ = lean_unsigned_to_nat(32u);
v___x_3884_ = lean_mk_empty_array_with_capacity(v___x_3883_);
lean_dec_ref(v___x_3884_);
v___x_3885_ = lean_unsigned_to_nat(0u);
v___x_3886_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3887_ = lean_ctor_get(v_log_3882_, 1);
v_isSharedCheck_3896_ = !lean_is_exclusive(v_log_3882_);
if (v_isSharedCheck_3896_ == 0)
{
lean_object* v_unused_3897_; lean_object* v_unused_3898_; 
v_unused_3897_ = lean_ctor_get(v_log_3882_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_log_3882_, 0);
lean_dec(v_unused_3898_);
v___x_3889_ = v_log_3882_;
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_unreported_3887_);
lean_dec(v_log_3882_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3896_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3894_; 
v___x_3891_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3887_, v___x_3886_, v___x_3885_);
lean_dec_ref(v_unreported_3887_);
v___x_3892_ = l_Lean_NameSet_empty;
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 2, v___x_3892_);
lean_ctor_set(v___x_3889_, 1, v___x_3891_);
lean_ctor_set(v___x_3889_, 0, v___x_3886_);
v___x_3894_ = v___x_3889_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3886_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3895_, 2, v___x_3892_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3899_, size_t v_i_3900_, size_t v_stop_3901_, lean_object* v_b_3902_){
_start:
{
lean_object* v___y_3904_; uint8_t v___x_3908_; 
v___x_3908_ = lean_usize_dec_eq(v_i_3900_, v_stop_3901_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; uint8_t v_severity_3910_; 
v___x_3909_ = lean_array_uget_borrowed(v_as_3899_, v_i_3900_);
v_severity_3910_ = lean_ctor_get_uint8(v___x_3909_, sizeof(void*)*5 + 1);
if (v_severity_3910_ == 1)
{
lean_object* v___x_3911_; 
lean_inc(v___x_3909_);
v___x_3911_ = l_Lean_PersistentArray_push___redArg(v_b_3902_, v___x_3909_);
v___y_3904_ = v___x_3911_;
goto v___jp_3903_;
}
else
{
v___y_3904_ = v_b_3902_;
goto v___jp_3903_;
}
}
else
{
return v_b_3902_;
}
v___jp_3903_:
{
size_t v___x_3905_; size_t v___x_3906_; 
v___x_3905_ = ((size_t)1ULL);
v___x_3906_ = lean_usize_add(v_i_3900_, v___x_3905_);
v_i_3900_ = v___x_3906_;
v_b_3902_ = v___y_3904_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3899_ = stack[0].m_obj;
size_t v_i_3900_ = stack[1].m_num;
size_t v_stop_3901_ = stack[2].m_num;
lean_object* v_b_3902_ = stack[3].m_obj;
lean_object* v_res_3912_;
v_res_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3899_, v_i_3900_, v_stop_3901_, v_b_3902_);
stack->m_obj
 = v_res_3912_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3913_, lean_object* v_i_3914_, lean_object* v_stop_3915_, lean_object* v_b_3916_){
_start:
{
size_t v_i_boxed_3917_; size_t v_stop_boxed_3918_; lean_object* v_res_3919_; 
v_i_boxed_3917_ = lean_unbox_usize(v_i_3914_);
lean_dec(v_i_3914_);
v_stop_boxed_3918_ = lean_unbox_usize(v_stop_3915_);
lean_dec(v_stop_3915_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3913_, v_i_boxed_3917_, v_stop_boxed_3918_, v_b_3916_);
lean_dec_ref(v_as_3913_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3920_, lean_object* v_x_3921_){
_start:
{
if (lean_obj_tag(v_x_3920_) == 0)
{
lean_object* v_cs_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_cs_3922_ = lean_ctor_get(v_x_3920_, 0);
v___x_3923_ = lean_unsigned_to_nat(0u);
v___x_3924_ = lean_array_get_size(v_cs_3922_);
v___x_3925_ = lean_nat_dec_lt(v___x_3923_, v___x_3924_);
if (v___x_3925_ == 0)
{
return v_x_3921_;
}
else
{
size_t v___x_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = ((size_t)0ULL);
v___x_3927_ = lean_usize_of_nat(v___x_3924_);
v___x_3928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3922_, v___x_3926_, v___x_3927_, v_x_3921_);
return v___x_3928_;
}
}
else
{
lean_object* v_vs_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; uint8_t v___x_3932_; 
v_vs_3929_ = lean_ctor_get(v_x_3920_, 0);
v___x_3930_ = lean_unsigned_to_nat(0u);
v___x_3931_ = lean_array_get_size(v_vs_3929_);
v___x_3932_ = lean_nat_dec_lt(v___x_3930_, v___x_3931_);
if (v___x_3932_ == 0)
{
return v_x_3921_;
}
else
{
size_t v___x_3933_; size_t v___x_3934_; lean_object* v___x_3935_; 
v___x_3933_ = ((size_t)0ULL);
v___x_3934_ = lean_usize_of_nat(v___x_3931_);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3929_, v___x_3933_, v___x_3934_, v_x_3921_);
return v___x_3935_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3936_, size_t v_i_3937_, size_t v_stop_3938_, lean_object* v_b_3939_){
_start:
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_usize_dec_eq(v_i_3937_, v_stop_3938_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; lean_object* v___x_3942_; size_t v___x_3943_; size_t v___x_3944_; 
v___x_3941_ = lean_array_uget_borrowed(v_as_3936_, v_i_3937_);
v___x_3942_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3941_, v_b_3939_);
v___x_3943_ = ((size_t)1ULL);
v___x_3944_ = lean_usize_add(v_i_3937_, v___x_3943_);
v_i_3937_ = v___x_3944_;
v_b_3939_ = v___x_3942_;
goto _start;
}
else
{
return v_b_3939_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3936_ = stack[0].m_obj;
size_t v_i_3937_ = stack[1].m_num;
size_t v_stop_3938_ = stack[2].m_num;
lean_object* v_b_3939_ = stack[3].m_obj;
lean_object* v_res_3946_;
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3936_, v_i_3937_, v_stop_3938_, v_b_3939_);
stack->m_obj
 = v_res_3946_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3947_, lean_object* v_i_3948_, lean_object* v_stop_3949_, lean_object* v_b_3950_){
_start:
{
size_t v_i_boxed_3951_; size_t v_stop_boxed_3952_; lean_object* v_res_3953_; 
v_i_boxed_3951_ = lean_unbox_usize(v_i_3948_);
lean_dec(v_i_3948_);
v_stop_boxed_3952_ = lean_unbox_usize(v_stop_3949_);
lean_dec(v_stop_3949_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3947_, v_i_boxed_3951_, v_stop_boxed_3952_, v_b_3950_);
lean_dec_ref(v_as_3947_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3954_, lean_object* v_x_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3954_, v_x_3955_);
lean_dec_ref(v_x_3954_);
return v_res_3956_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3957_, size_t v_x_3958_, size_t v_x_3959_, lean_object* v_x_3960_){
_start:
{
if (lean_obj_tag(v_x_3957_) == 0)
{
lean_object* v_cs_3961_; lean_object* v___x_3962_; size_t v___x_3963_; lean_object* v_j_3964_; lean_object* v___x_3965_; size_t v___x_3966_; size_t v___x_3967_; size_t v___x_3968_; size_t v___x_3969_; size_t v___x_3970_; size_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v_cs_3961_ = lean_ctor_get(v_x_3957_, 0);
v___x_3962_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3963_ = lean_usize_shift_right(v_x_3958_, v_x_3959_);
v_j_3964_ = lean_usize_to_nat(v___x_3963_);
v___x_3965_ = lean_array_get_borrowed(v___x_3962_, v_cs_3961_, v_j_3964_);
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_shift_left(v___x_3966_, v_x_3959_);
v___x_3968_ = lean_usize_sub(v___x_3967_, v___x_3966_);
v___x_3969_ = lean_usize_land(v_x_3958_, v___x_3968_);
v___x_3970_ = ((size_t)5ULL);
v___x_3971_ = lean_usize_sub(v_x_3959_, v___x_3970_);
v___x_3972_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3965_, v___x_3969_, v___x_3971_, v_x_3960_);
v___x_3973_ = lean_unsigned_to_nat(1u);
v___x_3974_ = lean_nat_add(v_j_3964_, v___x_3973_);
lean_dec(v_j_3964_);
v___x_3975_ = lean_array_get_size(v_cs_3961_);
v___x_3976_ = lean_nat_dec_lt(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_dec(v___x_3974_);
return v___x_3972_;
}
else
{
size_t v___x_3977_; size_t v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_usize_of_nat(v___x_3974_);
lean_dec(v___x_3974_);
v___x_3978_ = lean_usize_of_nat(v___x_3975_);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3961_, v___x_3977_, v___x_3978_, v___x_3972_);
return v___x_3979_;
}
}
else
{
lean_object* v_vs_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v_vs_3980_ = lean_ctor_get(v_x_3957_, 0);
v___x_3981_ = lean_usize_to_nat(v_x_3958_);
v___x_3982_ = lean_array_get_size(v_vs_3980_);
v___x_3983_ = lean_nat_dec_lt(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_dec(v___x_3981_);
return v_x_3960_;
}
else
{
size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = lean_usize_of_nat(v___x_3981_);
lean_dec(v___x_3981_);
v___x_3985_ = lean_usize_of_nat(v___x_3982_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3980_, v___x_3984_, v___x_3985_, v_x_3960_);
return v___x_3986_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3957_ = stack[0].m_obj;
size_t v_x_3958_ = stack[1].m_num;
size_t v_x_3959_ = stack[2].m_num;
lean_object* v_x_3960_ = stack[3].m_obj;
lean_object* v_res_3987_;
v_res_3987_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3957_, v_x_3958_, v_x_3959_, v_x_3960_);
stack->m_obj
 = v_res_3987_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_, lean_object* v_x_3991_){
_start:
{
size_t v_x_1184__boxed_3992_; size_t v_x_1185__boxed_3993_; lean_object* v_res_3994_; 
v_x_1184__boxed_3992_ = lean_unbox_usize(v_x_3989_);
lean_dec(v_x_3989_);
v_x_1185__boxed_3993_ = lean_unbox_usize(v_x_3990_);
lean_dec(v_x_3990_);
v_res_3994_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3988_, v_x_1184__boxed_3992_, v_x_1185__boxed_3993_, v_x_3991_);
lean_dec_ref(v_x_3988_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3995_, lean_object* v_init_3996_, lean_object* v_start_3997_){
_start:
{
lean_object* v___x_3998_; uint8_t v___x_3999_; 
v___x_3998_ = lean_unsigned_to_nat(0u);
v___x_3999_ = lean_nat_dec_eq(v_start_3997_, v___x_3998_);
if (v___x_3999_ == 0)
{
lean_object* v_root_4000_; lean_object* v_tail_4001_; size_t v_shift_4002_; lean_object* v_tailOff_4003_; uint8_t v___x_4004_; 
v_root_4000_ = lean_ctor_get(v_t_3995_, 0);
v_tail_4001_ = lean_ctor_get(v_t_3995_, 1);
v_shift_4002_ = lean_ctor_get_usize(v_t_3995_, 4);
v_tailOff_4003_ = lean_ctor_get(v_t_3995_, 3);
v___x_4004_ = lean_nat_dec_le(v_tailOff_4003_, v_start_3997_);
if (v___x_4004_ == 0)
{
size_t v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4005_ = lean_usize_of_nat(v_start_3997_);
v___x_4006_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_4000_, v___x_4005_, v_shift_4002_, v_init_3996_);
v___x_4007_ = lean_array_get_size(v_tail_4001_);
v___x_4008_ = lean_nat_dec_lt(v___x_3998_, v___x_4007_);
if (v___x_4008_ == 0)
{
return v___x_4006_;
}
else
{
size_t v___x_4009_; size_t v___x_4010_; lean_object* v___x_4011_; 
v___x_4009_ = ((size_t)0ULL);
v___x_4010_ = lean_usize_of_nat(v___x_4007_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4001_, v___x_4009_, v___x_4010_, v___x_4006_);
return v___x_4011_;
}
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4012_ = lean_nat_sub(v_start_3997_, v_tailOff_4003_);
v___x_4013_ = lean_array_get_size(v_tail_4001_);
v___x_4014_ = lean_nat_dec_lt(v___x_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_dec(v___x_4012_);
return v_init_3996_;
}
else
{
size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_usize_of_nat(v___x_4012_);
lean_dec(v___x_4012_);
v___x_4016_ = lean_usize_of_nat(v___x_4013_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4001_, v___x_4015_, v___x_4016_, v_init_3996_);
return v___x_4017_;
}
}
}
else
{
lean_object* v_root_4018_; lean_object* v_tail_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v_root_4018_ = lean_ctor_get(v_t_3995_, 0);
v_tail_4019_ = lean_ctor_get(v_t_3995_, 1);
v___x_4020_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_4018_, v_init_3996_);
v___x_4021_ = lean_array_get_size(v_tail_4019_);
v___x_4022_ = lean_nat_dec_lt(v___x_3998_, v___x_4021_);
if (v___x_4022_ == 0)
{
return v___x_4020_;
}
else
{
size_t v___x_4023_; size_t v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = ((size_t)0ULL);
v___x_4024_ = lean_usize_of_nat(v___x_4021_);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_4019_, v___x_4023_, v___x_4024_, v___x_4020_);
return v___x_4025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_4026_, lean_object* v_init_4027_, lean_object* v_start_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_4026_, v_init_4027_, v_start_4028_);
lean_dec(v_start_4028_);
lean_dec_ref(v_t_4026_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_unreported_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4044_; 
v___x_4031_ = lean_unsigned_to_nat(32u);
v___x_4032_ = lean_mk_empty_array_with_capacity(v___x_4031_);
lean_dec_ref(v___x_4032_);
v___x_4033_ = lean_unsigned_to_nat(0u);
v___x_4034_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_4035_ = lean_ctor_get(v_log_4030_, 1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_log_4030_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; lean_object* v_unused_4046_; 
v_unused_4045_ = lean_ctor_get(v_log_4030_, 2);
lean_dec(v_unused_4045_);
v_unused_4046_ = lean_ctor_get(v_log_4030_, 0);
lean_dec(v_unused_4046_);
v___x_4037_ = v_log_4030_;
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_unreported_4035_);
lean_dec(v_log_4030_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4042_; 
v___x_4039_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_4035_, v___x_4034_, v___x_4033_);
lean_dec_ref(v_unreported_4035_);
v___x_4040_ = l_Lean_NameSet_empty;
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 2, v___x_4040_);
lean_ctor_set(v___x_4037_, 1, v___x_4039_);
lean_ctor_set(v___x_4037_, 0, v___x_4034_);
v___x_4042_ = v___x_4037_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4043_, 1, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4043_, 2, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_4047_, lean_object* v_log_4048_, lean_object* v_f_4049_){
_start:
{
lean_object* v_unreported_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v_unreported_4050_ = lean_ctor_get(v_log_4048_, 1);
lean_inc_ref(v_unreported_4050_);
lean_dec_ref(v_log_4048_);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = l_Lean_PersistentArray_forM___redArg(v_inst_4047_, v_unreported_4050_, v_f_4049_, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_4053_, lean_object* v_inst_4054_, lean_object* v_log_4055_, lean_object* v_f_4056_){
_start:
{
lean_object* v___x_4057_; 
v___x_4057_ = l_Lean_MessageLog_forM___redArg(v_inst_4054_, v_log_4055_, v_f_4056_);
return v___x_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_4058_){
_start:
{
lean_object* v_unreported_4059_; lean_object* v___x_4060_; 
v_unreported_4059_ = lean_ctor_get(v_log_4058_, 1);
v___x_4060_ = l_Lean_PersistentArray_toList___redArg(v_unreported_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_MessageLog_toList(v_log_4061_);
lean_dec_ref(v_log_4061_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_4063_){
_start:
{
lean_object* v_unreported_4064_; lean_object* v___x_4065_; 
v_unreported_4064_ = lean_ctor_get(v_log_4063_, 1);
v___x_4065_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_MessageLog_toArray(v_log_4066_);
lean_dec_ref(v_log_4066_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4068_){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = lean_unsigned_to_nat(2u);
v___x_4070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
lean_ctor_set(v___x_4070_, 1, v_msg_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4071_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
lean_ctor_set(v___x_4073_, 1, v_msg_4071_);
v___x_4074_ = l_Lean_MessageData_nestD(v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4075_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = l_Lean_MessageData_ofExpr(v_e_4075_);
v___x_4077_ = l_Lean_indentD(v___x_4076_);
return v___x_4077_;
}
}
lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4078_, lean_object* v_msg_4079_){
_start:
{
lean_object* v_env_4081_; lean_object* v_mctx_4082_; lean_object* v_lctx_4083_; lean_object* v_opts_4084_; lean_object* v_currNamespace_4085_; lean_object* v_openDecls_4086_; lean_object* v___x_4087_; lean_object* v_msg_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_env_4081_ = lean_ctor_get(v_ctx_4078_, 0);
v_mctx_4082_ = lean_ctor_get(v_ctx_4078_, 1);
v_lctx_4083_ = lean_ctor_get(v_ctx_4078_, 2);
v_opts_4084_ = lean_ctor_get(v_ctx_4078_, 3);
v_currNamespace_4085_ = lean_ctor_get(v_ctx_4078_, 4);
v_openDecls_4086_ = lean_ctor_get(v_ctx_4078_, 5);
lean_inc(v_openDecls_4086_);
lean_inc(v_currNamespace_4085_);
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v_currNamespace_4085_);
lean_ctor_set(v___x_4087_, 1, v_openDecls_4086_);
v_msg_4088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4088_, 0, v___x_4087_);
lean_ctor_set(v_msg_4088_, 1, v_msg_4079_);
lean_inc_ref(v_opts_4084_);
lean_inc_ref(v_lctx_4083_);
lean_inc_ref(v_mctx_4082_);
lean_inc_ref(v_env_4081_);
v___x_4089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4089_, 0, v_env_4081_);
lean_ctor_set(v___x_4089_, 1, v_mctx_4082_);
lean_ctor_set(v___x_4089_, 2, v_lctx_4083_);
lean_ctor_set(v___x_4089_, 3, v_opts_4084_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v___x_4091_ = l_Lean_MessageData_format(v_msg_4088_, v___x_4090_);
v___x_4092_ = l_Std_Format_defWidth;
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = l_Std_Format_pretty(v___x_4091_, v___x_4092_, v___x_4093_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT void l___private_Lean_Message_0__Lean_MessageData_formatExpensively_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_4078_ = stack[0].m_obj;
lean_object* v_msg_4079_ = stack[1].m_obj;
lean_object* v_res_4095_;
v_res_4095_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4078_, v_msg_4079_);
stack->m_obj
 = v_res_4095_;
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4096_, lean_object* v_msg_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_res_4099_; 
v_res_4099_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4096_, v_msg_4097_);
lean_dec_ref(v_ctx_4096_);
return v_res_4099_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4100_, lean_object* v_a_4101_, uint8_t v_b_4102_){
_start:
{
lean_object* v_str_4103_; lean_object* v_startInclusive_4104_; lean_object* v_endExclusive_4105_; lean_object* v___x_4106_; uint8_t v_decide_4107_; 
v_str_4103_ = lean_ctor_get(v_s_4100_, 0);
v_startInclusive_4104_ = lean_ctor_get(v_s_4100_, 1);
v_endExclusive_4105_ = lean_ctor_get(v_s_4100_, 2);
v___x_4106_ = lean_nat_sub(v_endExclusive_4105_, v_startInclusive_4104_);
v_decide_4107_ = lean_nat_dec_eq(v_a_4101_, v___x_4106_);
lean_dec(v___x_4106_);
if (v_decide_4107_ == 0)
{
lean_object* v___x_4108_; uint32_t v___x_4109_; uint32_t v___x_4110_; uint8_t v___x_4111_; 
v___x_4108_ = lean_nat_add(v_startInclusive_4104_, v_a_4101_);
lean_dec(v_a_4101_);
v___x_4109_ = lean_string_utf8_get_fast(v_str_4103_, v___x_4108_);
v___x_4110_ = 10;
v___x_4111_ = lean_uint32_dec_eq(v___x_4109_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_string_utf8_next_fast(v_str_4103_, v___x_4108_);
lean_dec(v___x_4108_);
v___x_4113_ = lean_nat_sub(v___x_4112_, v_startInclusive_4104_);
v_a_4101_ = v___x_4113_;
v_b_4102_ = v___x_4111_;
goto _start;
}
else
{
lean_dec(v___x_4108_);
return v___x_4111_;
}
}
else
{
lean_dec(v_a_4101_);
return v_b_4102_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4100_ = stack[0].m_obj;
lean_object* v_a_4101_ = stack[1].m_obj;
uint8_t v_b_4102_ = stack[2].m_num;
uint8_t v_res_4115_;
v_res_4115_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4100_, v_a_4101_, v_b_4102_);
stack->m_num = v_res_4115_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4116_, lean_object* v_a_4117_, lean_object* v_b_4118_){
_start:
{
uint8_t v_b_boxed_4119_; uint8_t v_res_4120_; lean_object* v_r_4121_; 
v_b_boxed_4119_ = lean_unbox(v_b_4118_);
v_res_4120_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4116_, v_a_4117_, v_b_boxed_4119_);
lean_dec_ref(v_s_4116_);
v_r_4121_ = lean_box(v_res_4120_);
return v_r_4121_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4122_){
_start:
{
lean_object* v_searcher_4123_; uint8_t v___x_4124_; uint8_t v___x_4125_; 
v_searcher_4123_ = lean_unsigned_to_nat(0u);
v___x_4124_ = 0;
v___x_4125_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4122_, v_searcher_4123_, v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_inlineExpr_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4122_ = stack[0].m_obj;
uint8_t v_res_4126_;
v_res_4126_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4122_);
stack->m_num = v_res_4126_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4127_){
_start:
{
uint8_t v_res_4128_; lean_object* v_r_4129_; 
v_res_4128_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4127_);
lean_dec_ref(v_s_4127_);
v_r_4129_ = lean_box(v_res_4128_);
return v_r_4129_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4130_, lean_object* v_val_4131_, lean_object* v_a_4132_, lean_object* v_b_4133_){
_start:
{
uint8_t v_decide_4134_; 
v_decide_4134_ = lean_nat_dec_eq(v_a_4132_, v___x_4130_);
if (v_decide_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4135_ = lean_string_utf8_next_fast(v_val_4131_, v_a_4132_);
lean_dec(v_a_4132_);
v___x_4136_ = lean_unsigned_to_nat(1u);
v___x_4137_ = lean_nat_add(v_b_4133_, v___x_4136_);
lean_dec(v_b_4133_);
v_a_4132_ = v___x_4135_;
v_b_4133_ = v___x_4137_;
goto _start;
}
else
{
lean_dec(v_a_4132_);
return v_b_4133_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4139_, lean_object* v_val_4140_, lean_object* v_a_4141_, lean_object* v_b_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4139_, v_val_4140_, v_a_4141_, v_b_4142_);
lean_dec_ref(v_val_4140_);
lean_dec(v___x_4139_);
return v_res_4143_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4144_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4145_ = l_Lean_MessageData_ofFormat(v___x_4144_);
return v___x_4145_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_4150_ = l_Lean_MessageData_ofFormat(v___x_4149_);
return v___x_4150_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_4155_ = l_Lean_MessageData_ofFormat(v___x_4154_);
return v___x_4155_;
}
}
lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4156_, lean_object* v_maxInlineLength_4157_, lean_object* v_ctx_4158_){
_start:
{
lean_object* v_msg_4160_; lean_object* v___x_4161_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v_msg_4160_ = l_Lean_MessageData_ofExpr(v_e_4156_);
lean_inc_ref(v_msg_4160_);
v___x_4161_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4158_, v_msg_4160_);
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = lean_string_utf8_byte_size(v___x_4161_);
lean_inc_ref(v___x_4161_);
v___x_4168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4161_);
lean_ctor_set(v___x_4168_, 1, v___x_4166_);
lean_ctor_set(v___x_4168_, 2, v___x_4167_);
v___x_4169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4167_, v___x_4161_, v___x_4166_, v___x_4166_);
lean_dec_ref(v___x_4161_);
v___x_4170_ = lean_nat_dec_lt(v_maxInlineLength_4157_, v___x_4169_);
lean_dec(v___x_4169_);
if (v___x_4170_ == 0)
{
uint8_t v___x_4171_; 
v___x_4171_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4168_);
lean_dec_ref_known(v___x_4168_, 3);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4172_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v_msg_4160_);
v___x_4174_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4173_);
lean_ctor_set(v___x_4175_, 1, v___x_4174_);
return v___x_4175_;
}
else
{
goto v___jp_4162_;
}
}
else
{
lean_dec_ref_known(v___x_4168_, 3);
goto v___jp_4162_;
}
v___jp_4162_:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v___x_4163_ = l_Lean_indentD(v_msg_4160_);
v___x_4164_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4163_);
lean_ctor_set(v___x_4165_, 1, v___x_4164_);
return v___x_4165_;
}
}
}
LEAN_EXPORT void l_Lean_inlineExpr___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4156_ = stack[0].m_obj;
lean_object* v_maxInlineLength_4157_ = stack[1].m_obj;
lean_object* v_ctx_4158_ = stack[2].m_obj;
lean_object* v_res_4176_;
v_res_4176_ = l_Lean_inlineExpr___lam__0(v_e_4156_, v_maxInlineLength_4157_, v_ctx_4158_);
stack->m_obj
 = v_res_4176_;
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4177_, lean_object* v_maxInlineLength_4178_, lean_object* v_ctx_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_inlineExpr___lam__0(v_e_4177_, v_maxInlineLength_4178_, v_ctx_4179_);
lean_dec_ref(v_ctx_4179_);
lean_dec(v_maxInlineLength_4178_);
return v_res_4181_;
}
}
lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4182_, lean_object* v_x_4183_){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4185_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4186_ = l_Lean_MessageData_ofExpr(v_e_4182_);
v___x_4187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4185_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
return v___x_4189_;
}
}
LEAN_EXPORT void l_Lean_inlineExpr___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4182_ = stack[0].m_obj;
lean_object* v_x_4183_ = stack[1].m_obj;
lean_object* v_res_4190_;
v_res_4190_ = l_Lean_inlineExpr___lam__2(v_e_4182_, v_x_4183_);
stack->m_obj
 = v_res_4190_;
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_inlineExpr___lam__2(v_e_4191_, v_x_4192_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4195_, lean_object* v_maxInlineLength_4196_){
_start:
{
lean_object* v___f_4197_; lean_object* v___f_4198_; lean_object* v___f_4199_; lean_object* v___x_4200_; 
lean_inc_ref_n(v_e_4195_, 2);
v___f_4197_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4197_, 0, v_e_4195_);
lean_closure_set(v___f_4197_, 1, v_maxInlineLength_4196_);
v___f_4198_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4198_, 0, v_e_4195_);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4199_, 0, v_e_4195_);
v___x_4200_ = l_Lean_MessageData_lazy(v___f_4197_, v___f_4198_, v___f_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v_val_4203_, lean_object* v_inst_4204_, lean_object* v_R_4205_, lean_object* v_a_4206_, lean_object* v_b_4207_, lean_object* v_c_4208_){
_start:
{
lean_object* v___x_4209_; 
v___x_4209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4201_, v_val_4203_, v_a_4206_, v_b_4207_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v_val_4212_, lean_object* v_inst_4213_, lean_object* v_R_4214_, lean_object* v_a_4215_, lean_object* v_b_4216_, lean_object* v_c_4217_){
_start:
{
lean_object* v_res_4218_; 
v_res_4218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4210_, v___x_4211_, v_val_4212_, v_inst_4213_, v_R_4214_, v_a_4215_, v_b_4216_, v_c_4217_);
lean_dec_ref(v_val_4212_);
lean_dec_ref(v___x_4211_);
lean_dec(v___x_4210_);
return v_res_4218_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4219_, lean_object* v_inst_4220_, lean_object* v_R_4221_, lean_object* v_a_4222_, uint8_t v_b_4223_, lean_object* v_c_4224_){
_start:
{
uint8_t v___x_4225_; 
v___x_4225_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4219_, v_a_4222_, v_b_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_4219_ = stack[0].m_obj;
lean_object* v_a_4222_ = stack[3].m_obj;
uint8_t v_b_4223_ = stack[4].m_num;
uint8_t v_res_4226_;
v_res_4226_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4219_, lean_box(0), lean_box(0), v_a_4222_, v_b_4223_, lean_box(0));
stack->m_num = v_res_4226_;
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
lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4241_, lean_object* v_maxInlineLength_4242_, lean_object* v_ctx_4243_){
_start:
{
lean_object* v_msg_4245_; lean_object* v___x_4246_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v_msg_4245_ = l_Lean_MessageData_ofExpr(v_e_4241_);
lean_inc_ref(v_msg_4245_);
v___x_4246_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4243_, v_msg_4245_);
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_string_utf8_byte_size(v___x_4246_);
lean_inc_ref(v___x_4246_);
v___x_4251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4246_);
lean_ctor_set(v___x_4251_, 1, v___x_4249_);
lean_ctor_set(v___x_4251_, 2, v___x_4250_);
v___x_4252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4250_, v___x_4246_, v___x_4249_, v___x_4249_);
lean_dec_ref(v___x_4246_);
v___x_4253_ = lean_nat_dec_lt(v_maxInlineLength_4242_, v___x_4252_);
lean_dec(v___x_4252_);
if (v___x_4253_ == 0)
{
uint8_t v___x_4254_; 
v___x_4254_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4251_);
lean_dec_ref_known(v___x_4251_, 3);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4255_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v_msg_4245_);
v___x_4257_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
return v___x_4258_;
}
else
{
goto v___jp_4247_;
}
}
else
{
lean_dec_ref_known(v___x_4251_, 3);
goto v___jp_4247_;
}
v___jp_4247_:
{
lean_object* v___x_4248_; 
v___x_4248_ = l_Lean_indentD(v_msg_4245_);
return v___x_4248_;
}
}
}
LEAN_EXPORT void l_Lean_inlineExprTrailing___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4241_ = stack[0].m_obj;
lean_object* v_maxInlineLength_4242_ = stack[1].m_obj;
lean_object* v_ctx_4243_ = stack[2].m_obj;
lean_object* v_res_4259_;
v_res_4259_ = l_Lean_inlineExprTrailing___lam__0(v_e_4241_, v_maxInlineLength_4242_, v_ctx_4243_);
stack->m_obj
 = v_res_4259_;
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
lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4265_, lean_object* v_x_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4268_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
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
LEAN_EXPORT void l_Lean_inlineExprTrailing___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4265_ = stack[0].m_obj;
lean_object* v_x_4266_ = stack[1].m_obj;
lean_object* v_res_4273_;
v_res_4273_ = l_Lean_inlineExprTrailing___lam__2(v_e_4265_, v_x_4266_);
stack->m_obj
 = v_res_4273_;
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4274_, lean_object* v_x_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_inlineExprTrailing___lam__2(v_e_4274_, v_x_4275_);
return v_res_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4278_, lean_object* v_maxInlineLength_4279_){
_start:
{
lean_object* v___f_4280_; lean_object* v___f_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; 
lean_inc_ref_n(v_e_4278_, 2);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4280_, 0, v_e_4278_);
lean_closure_set(v___f_4280_, 1, v_maxInlineLength_4279_);
v___f_4281_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4281_, 0, v_e_4278_);
v___f_4282_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4282_, 0, v_e_4278_);
v___x_4283_ = l_Lean_MessageData_lazy(v___f_4280_, v___f_4281_, v___f_4282_);
return v___x_4283_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4288_ = l_Lean_MessageData_ofFormat(v___x_4287_);
return v___x_4288_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4293_ = l_Lean_MessageData_ofFormat(v___x_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4294_){
_start:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4295_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v_msg_4294_);
v___x_4297_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4299_, lean_object* v_inst_4300_, lean_object* v_msg_4301_){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = lean_apply_1(v_inst_4299_, v_msg_4301_);
v___x_4303_ = lean_apply_2(v_inst_4300_, lean_box(0), v___x_4302_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4304_, lean_object* v_inst_4305_){
_start:
{
lean_object* v___f_4306_; 
v___f_4306_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4306_, 0, v_inst_4305_);
lean_closure_set(v___f_4306_, 1, v_inst_4304_);
return v___f_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4307_, lean_object* v_n_4308_, lean_object* v_inst_4309_, lean_object* v_inst_4310_){
_start:
{
lean_object* v___f_4311_; 
v___f_4311_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4311_, 0, v_inst_4310_);
lean_closure_set(v___f_4311_, 1, v_inst_4309_);
return v___f_4311_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4312_ = lean_unsigned_to_nat(32u);
v___x_4313_ = lean_mk_empty_array_with_capacity(v___x_4312_);
v___x_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
return v___x_4314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4315_ = ((size_t)5ULL);
v___x_4316_ = lean_unsigned_to_nat(0u);
v___x_4317_ = lean_unsigned_to_nat(32u);
v___x_4318_ = lean_mk_empty_array_with_capacity(v___x_4317_);
v___x_4319_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4320_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
lean_ctor_set(v___x_4320_, 1, v___x_4318_);
lean_ctor_set(v___x_4320_, 2, v___x_4316_);
lean_ctor_set(v___x_4320_, 3, v___x_4316_);
lean_ctor_set_usize(v___x_4320_, 4, v___x_4315_);
return v___x_4320_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4321_ = lean_box(1);
v___x_4322_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4323_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v___x_4322_);
lean_ctor_set(v___x_4324_, 2, v___x_4321_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4325_, lean_object* v_msgData_4326_, lean_object* v_toPure_4327_, lean_object* v_opts_4328_){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4329_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4330_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4331_, 0, v_env_4325_);
lean_ctor_set(v___x_4331_, 1, v___x_4329_);
lean_ctor_set(v___x_4331_, 2, v___x_4330_);
lean_ctor_set(v___x_4331_, 3, v_opts_4328_);
v___x_4332_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v_msgData_4326_);
v___x_4333_ = lean_apply_2(v_toPure_4327_, lean_box(0), v___x_4332_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_inst_4334_, lean_object* v_msgData_4335_, lean_object* v_toPure_4336_, lean_object* v_toBind_4337_, lean_object* v_____do__lift_4338_){
_start:
{
lean_object* v_getOptionsUnrestricted_4339_; uint8_t v___x_4340_; lean_object* v_env_4341_; lean_object* v___f_4342_; lean_object* v___x_4343_; 
v_getOptionsUnrestricted_4339_ = lean_ctor_get(v_inst_4334_, 1);
lean_inc(v_getOptionsUnrestricted_4339_);
lean_dec_ref(v_inst_4334_);
v___x_4340_ = 0;
v_env_4341_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4338_, v___x_4340_);
v___f_4342_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4342_, 0, v_env_4341_);
lean_closure_set(v___f_4342_, 1, v_msgData_4335_);
lean_closure_set(v___f_4342_, 2, v_toPure_4336_);
v___x_4343_ = lean_apply_4(v_toBind_4337_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4339_, v___f_4342_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4344_, lean_object* v_inst_4345_, lean_object* v_inst_4346_, lean_object* v_msgData_4347_){
_start:
{
lean_object* v_toApplicative_4348_; lean_object* v_toBind_4349_; lean_object* v_getEnv_4350_; lean_object* v_toPure_4351_; lean_object* v___f_4352_; lean_object* v___x_4353_; 
v_toApplicative_4348_ = lean_ctor_get(v_inst_4344_, 0);
lean_inc_ref(v_toApplicative_4348_);
v_toBind_4349_ = lean_ctor_get(v_inst_4344_, 1);
lean_inc_n(v_toBind_4349_, 2);
lean_dec_ref(v_inst_4344_);
v_getEnv_4350_ = lean_ctor_get(v_inst_4345_, 0);
lean_inc(v_getEnv_4350_);
lean_dec_ref(v_inst_4345_);
v_toPure_4351_ = lean_ctor_get(v_toApplicative_4348_, 1);
lean_inc(v_toPure_4351_);
lean_dec_ref(v_toApplicative_4348_);
v___f_4352_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4352_, 0, v_inst_4346_);
lean_closure_set(v___f_4352_, 1, v_msgData_4347_);
lean_closure_set(v___f_4352_, 2, v_toPure_4351_);
lean_closure_set(v___f_4352_, 3, v_toBind_4349_);
v___x_4353_ = lean_apply_4(v_toBind_4349_, lean_box(0), lean_box(0), v_getEnv_4350_, v___f_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4354_, lean_object* v_inst_4355_, lean_object* v_inst_4356_, lean_object* v_inst_4357_, lean_object* v_msgData_4358_){
_start:
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_addMessageContextPartial___redArg(v_inst_4355_, v_inst_4356_, v_inst_4357_, v_msgData_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4360_, lean_object* v_mctx_4361_, lean_object* v_lctx_4362_, lean_object* v_msgData_4363_, lean_object* v_toPure_4364_, lean_object* v_opts_4365_){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4366_, 0, v_env_4360_);
lean_ctor_set(v___x_4366_, 1, v_mctx_4361_);
lean_ctor_set(v___x_4366_, 2, v_lctx_4362_);
lean_ctor_set(v___x_4366_, 3, v_opts_4365_);
v___x_4367_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set(v___x_4367_, 1, v_msgData_4363_);
v___x_4368_ = lean_apply_2(v_toPure_4364_, lean_box(0), v___x_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_inst_4369_, lean_object* v_env_4370_, lean_object* v_mctx_4371_, lean_object* v_msgData_4372_, lean_object* v_toPure_4373_, lean_object* v_toBind_4374_, lean_object* v_lctx_4375_){
_start:
{
lean_object* v_getOptionsUnrestricted_4376_; lean_object* v___f_4377_; lean_object* v___x_4378_; 
v_getOptionsUnrestricted_4376_ = lean_ctor_get(v_inst_4369_, 1);
lean_inc(v_getOptionsUnrestricted_4376_);
lean_dec_ref(v_inst_4369_);
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4377_, 0, v_env_4370_);
lean_closure_set(v___f_4377_, 1, v_mctx_4371_);
lean_closure_set(v___f_4377_, 2, v_lctx_4375_);
lean_closure_set(v___f_4377_, 3, v_msgData_4372_);
lean_closure_set(v___f_4377_, 4, v_toPure_4373_);
v___x_4378_ = lean_apply_4(v_toBind_4374_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4376_, v___f_4377_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_inst_4379_, lean_object* v_env_4380_, lean_object* v_msgData_4381_, lean_object* v_toPure_4382_, lean_object* v_toBind_4383_, lean_object* v_inst_4384_, lean_object* v_mctx_4385_){
_start:
{
lean_object* v___f_4386_; lean_object* v___x_4387_; 
lean_inc(v_toBind_4383_);
v___f_4386_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4386_, 0, v_inst_4379_);
lean_closure_set(v___f_4386_, 1, v_env_4380_);
lean_closure_set(v___f_4386_, 2, v_mctx_4385_);
lean_closure_set(v___f_4386_, 3, v_msgData_4381_);
lean_closure_set(v___f_4386_, 4, v_toPure_4382_);
lean_closure_set(v___f_4386_, 5, v_toBind_4383_);
v___x_4387_ = lean_apply_4(v_toBind_4383_, lean_box(0), lean_box(0), v_inst_4384_, v___f_4386_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4388_, lean_object* v_inst_4389_, lean_object* v_msgData_4390_, lean_object* v_toPure_4391_, lean_object* v_toBind_4392_, lean_object* v_inst_4393_, lean_object* v_____do__lift_4394_){
_start:
{
lean_object* v_getMCtx_4395_; uint8_t v___x_4396_; lean_object* v_env_4397_; lean_object* v___f_4398_; lean_object* v___x_4399_; 
v_getMCtx_4395_ = lean_ctor_get(v_inst_4388_, 0);
lean_inc(v_getMCtx_4395_);
lean_dec_ref(v_inst_4388_);
v___x_4396_ = 0;
v_env_4397_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4394_, v___x_4396_);
lean_inc(v_toBind_4392_);
v___f_4398_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4398_, 0, v_inst_4389_);
lean_closure_set(v___f_4398_, 1, v_env_4397_);
lean_closure_set(v___f_4398_, 2, v_msgData_4390_);
lean_closure_set(v___f_4398_, 3, v_toPure_4391_);
lean_closure_set(v___f_4398_, 4, v_toBind_4392_);
lean_closure_set(v___f_4398_, 5, v_inst_4393_);
v___x_4399_ = lean_apply_4(v_toBind_4392_, lean_box(0), lean_box(0), v_getMCtx_4395_, v___f_4398_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg(lean_object* v_inst_4400_, lean_object* v_inst_4401_, lean_object* v_inst_4402_, lean_object* v_inst_4403_, lean_object* v_inst_4404_, lean_object* v_msgData_4405_){
_start:
{
lean_object* v_toApplicative_4406_; lean_object* v_toBind_4407_; lean_object* v_getEnv_4408_; lean_object* v_toPure_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; 
v_toApplicative_4406_ = lean_ctor_get(v_inst_4400_, 0);
lean_inc_ref(v_toApplicative_4406_);
v_toBind_4407_ = lean_ctor_get(v_inst_4400_, 1);
lean_inc_n(v_toBind_4407_, 2);
lean_dec_ref(v_inst_4400_);
v_getEnv_4408_ = lean_ctor_get(v_inst_4401_, 0);
lean_inc(v_getEnv_4408_);
lean_dec_ref(v_inst_4401_);
v_toPure_4409_ = lean_ctor_get(v_toApplicative_4406_, 1);
lean_inc(v_toPure_4409_);
lean_dec_ref(v_toApplicative_4406_);
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__3), 7, 6);
lean_closure_set(v___f_4410_, 0, v_inst_4402_);
lean_closure_set(v___f_4410_, 1, v_inst_4404_);
lean_closure_set(v___f_4410_, 2, v_msgData_4405_);
lean_closure_set(v___f_4410_, 3, v_toPure_4409_);
lean_closure_set(v___f_4410_, 4, v_toBind_4407_);
lean_closure_set(v___f_4410_, 5, v_inst_4403_);
v___x_4411_ = lean_apply_4(v_toBind_4407_, lean_box(0), lean_box(0), v_getEnv_4408_, v___f_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull(lean_object* v_m_4412_, lean_object* v_inst_4413_, lean_object* v_inst_4414_, lean_object* v_inst_4415_, lean_object* v_inst_4416_, lean_object* v_inst_4417_, lean_object* v_msgData_4418_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l_Lean_addMessageContextFull___redArg(v_inst_4413_, v_inst_4414_, v_inst_4415_, v_inst_4416_, v_inst_4417_, v_msgData_4418_);
return v___x_4419_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg(){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0));
return v___x_4423_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4424_;
v_res_4424_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
stack->m_obj
 = v_res_4424_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object* v___dummy_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v_res_4426_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4427_; 
v___x_4427_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v___x_4427_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4428_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4430_);
lean_dec_ref(v_s_4430_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4432_, lean_object* v___x_4433_, lean_object* v___x_4434_, lean_object* v_a_4435_, lean_object* v_b_4436_){
_start:
{
lean_object* v_it_4438_; lean_object* v_startInclusive_4439_; lean_object* v_endExclusive_4440_; 
if (lean_obj_tag(v_a_4435_) == 0)
{
lean_object* v_currPos_4446_; lean_object* v_searcher_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4470_; 
v_currPos_4446_ = lean_ctor_get(v_a_4435_, 0);
v_searcher_4447_ = lean_ctor_get(v_a_4435_, 1);
v_isSharedCheck_4470_ = !lean_is_exclusive(v_a_4435_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4449_ = v_a_4435_;
v_isShared_4450_ = v_isSharedCheck_4470_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_searcher_4447_);
lean_inc(v_currPos_4446_);
lean_dec(v_a_4435_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4470_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
uint8_t v_decide_4451_; 
v_decide_4451_ = lean_nat_dec_eq(v_searcher_4447_, v___x_4434_);
if (v_decide_4451_ == 0)
{
uint32_t v___x_4452_; uint32_t v___x_4453_; uint8_t v___x_4454_; 
v___x_4452_ = 10;
v___x_4453_ = lean_string_utf8_get_fast(v_str_4432_, v_searcher_4447_);
v___x_4454_ = lean_uint32_dec_eq(v___x_4453_, v___x_4452_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
v___x_4455_ = lean_string_utf8_next_fast(v_str_4432_, v_searcher_4447_);
lean_dec(v_searcher_4447_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v___x_4455_);
v___x_4457_ = v___x_4449_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_currPos_4446_);
lean_ctor_set(v_reuseFailAlloc_4459_, 1, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
v_a_4435_ = v___x_4457_;
goto _start;
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v_slice_4463_; lean_object* v_nextIt_4465_; 
v___x_4460_ = lean_string_utf8_next_fast(v_str_4432_, v_searcher_4447_);
v___x_4461_ = lean_nat_sub(v___x_4460_, v_searcher_4447_);
v___x_4462_ = lean_nat_add(v_searcher_4447_, v___x_4461_);
lean_dec(v___x_4461_);
v_slice_4463_ = l_String_Slice_subslice_x21(v___x_4433_, v_currPos_4446_, v_searcher_4447_);
lean_inc(v___x_4462_);
if (v_isShared_4450_ == 0)
{
lean_ctor_set(v___x_4449_, 1, v___x_4462_);
lean_ctor_set(v___x_4449_, 0, v___x_4462_);
v_nextIt_4465_ = v___x_4449_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4462_);
lean_ctor_set(v_reuseFailAlloc_4468_, 1, v___x_4462_);
v_nextIt_4465_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v_startInclusive_4466_; lean_object* v_endExclusive_4467_; 
v_startInclusive_4466_ = lean_ctor_get(v_slice_4463_, 0);
lean_inc(v_startInclusive_4466_);
v_endExclusive_4467_ = lean_ctor_get(v_slice_4463_, 1);
lean_inc(v_endExclusive_4467_);
lean_dec_ref(v_slice_4463_);
v_it_4438_ = v_nextIt_4465_;
v_startInclusive_4439_ = v_startInclusive_4466_;
v_endExclusive_4440_ = v_endExclusive_4467_;
goto v___jp_4437_;
}
}
}
else
{
lean_object* v___x_4469_; 
lean_del_object(v___x_4449_);
lean_dec(v_searcher_4447_);
v___x_4469_ = lean_box(1);
lean_inc(v___x_4434_);
v_it_4438_ = v___x_4469_;
v_startInclusive_4439_ = v_currPos_4446_;
v_endExclusive_4440_ = v___x_4434_;
goto v___jp_4437_;
}
}
}
else
{
lean_dec(v___x_4434_);
return v_b_4436_;
}
v___jp_4437_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4441_ = lean_string_utf8_extract_fast(v_str_4432_, v_startInclusive_4439_, v_endExclusive_4440_);
lean_dec(v_endExclusive_4440_);
lean_dec(v_startInclusive_4439_);
v___x_4442_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
v___x_4443_ = l_Lean_MessageData_ofFormat(v___x_4442_);
v___x_4444_ = lean_array_push(v_b_4436_, v___x_4443_);
v_a_4435_ = v_it_4438_;
v_b_4436_ = v___x_4444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4471_, lean_object* v___x_4472_, lean_object* v___x_4473_, lean_object* v_a_4474_, lean_object* v_b_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4471_, v___x_4472_, v___x_4473_, v_a_4474_, v_b_4475_);
lean_dec_ref(v___x_4472_);
lean_dec_ref(v_str_4471_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4479_){
_start:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v_lines_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4480_ = lean_unsigned_to_nat(0u);
v___x_4481_ = lean_string_utf8_byte_size(v_str_4479_);
lean_inc_ref(v_str_4479_);
v___x_4482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4482_, 0, v_str_4479_);
lean_ctor_set(v___x_4482_, 1, v___x_4480_);
lean_ctor_set(v___x_4482_, 2, v___x_4481_);
v_lines_4483_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
v___x_4484_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4479_, v___x_4482_, v___x_4481_, v_lines_4483_, v___x_4484_);
lean_dec_ref_known(v___x_4482_, 3);
lean_dec_ref(v_str_4479_);
v___x_4486_ = lean_array_to_list(v___x_4485_);
v___x_4487_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4488_ = l_Lean_MessageData_joinSep(v___x_4486_, v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4489_, lean_object* v___x_4490_, lean_object* v___x_4491_, lean_object* v_inst_4492_, lean_object* v_R_4493_, lean_object* v_a_4494_, lean_object* v_b_4495_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4489_, v___x_4490_, v___x_4491_, v_a_4494_, v_b_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4497_, lean_object* v___x_4498_, lean_object* v___x_4499_, lean_object* v_inst_4500_, lean_object* v_R_4501_, lean_object* v_a_4502_, lean_object* v_b_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4497_, v___x_4498_, v___x_4499_, v_inst_4500_, v_R_4501_, v_a_4502_, v_b_4503_);
lean_dec_ref(v___x_4498_);
lean_dec_ref(v_str_4497_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4505_){
_start:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4506_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4507_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4507_, 0, lean_box(0));
lean_closure_set(v___x_4507_, 1, lean_box(0));
lean_closure_set(v___x_4507_, 2, lean_box(0));
lean_closure_set(v___x_4507_, 3, v___x_4506_);
lean_closure_set(v___x_4507_, 4, v_inst_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4508_, lean_object* v_inst_4509_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4509_);
return v___x_4510_;
}
}
lean_object* l_Lean_instToMessageDataTSyntax___redArg(){
_start:
{
lean_object* v___f_4518_; 
v___f_4518_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4518_;
}
}
LEAN_EXPORT void l_Lean_instToMessageDataTSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4519_;
v_res_4519_ = l_Lean_instToMessageDataTSyntax___redArg();
stack->m_obj
 = v_res_4519_;
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object* v___dummy_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_instToMessageDataTSyntax___redArg();
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4522_){
_start:
{
lean_object* v___f_4523_; 
v___f_4523_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_instToMessageDataTSyntax(v_k_4524_);
lean_dec(v_k_4524_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4530_, lean_object* v_as_4531_){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_box(0);
v___x_4533_ = l_List_mapTR_loop___redArg(v_inst_4530_, v_as_4531_, v___x_4532_);
v___x_4534_ = l_Lean_MessageData_ofList(v___x_4533_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4535_){
_start:
{
lean_object* v___f_4536_; 
v___f_4536_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4536_, 0, v_inst_4535_);
return v___f_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4537_, lean_object* v_inst_4538_){
_start:
{
lean_object* v___f_4539_; 
v___f_4539_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4539_, 0, v_inst_4538_);
return v___f_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4540_, lean_object* v_as_4541_){
_start:
{
lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4542_ = lean_array_to_list(v_as_4541_);
v___x_4543_ = lean_box(0);
v___x_4544_ = l_List_mapTR_loop___redArg(v_inst_4540_, v___x_4542_, v___x_4543_);
v___x_4545_ = l_Lean_MessageData_ofList(v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4546_){
_start:
{
lean_object* v___f_4547_; 
v___f_4547_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4547_, 0, v_inst_4546_);
return v___f_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4548_, lean_object* v_inst_4549_){
_start:
{
lean_object* v___f_4550_; 
v___f_4550_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4550_, 0, v_inst_4549_);
return v___f_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4551_, lean_object* v_acc_4552_, lean_object* v_recur_4553_){
_start:
{
lean_object* v_array_4554_; lean_object* v_start_4555_; lean_object* v_stop_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4569_; 
v_array_4554_ = lean_ctor_get(v_it_4551_, 0);
v_start_4555_ = lean_ctor_get(v_it_4551_, 1);
v_stop_4556_ = lean_ctor_get(v_it_4551_, 2);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_it_4551_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4558_ = v_it_4551_;
v_isShared_4559_ = v_isSharedCheck_4569_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_stop_4556_);
lean_inc(v_start_4555_);
lean_inc(v_array_4554_);
lean_dec(v_it_4551_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4569_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
uint8_t v___x_4560_; 
v___x_4560_ = lean_nat_dec_lt(v_start_4555_, v_stop_4556_);
if (v___x_4560_ == 0)
{
lean_del_object(v___x_4558_);
lean_dec(v_stop_4556_);
lean_dec(v_start_4555_);
lean_dec_ref(v_array_4554_);
lean_dec_ref(v_recur_4553_);
return v_acc_4552_;
}
else
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4561_ = lean_unsigned_to_nat(1u);
v___x_4562_ = lean_nat_add(v_start_4555_, v___x_4561_);
lean_inc_ref(v_array_4554_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 1, v___x_4562_);
v___x_4564_ = v___x_4558_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_array_4554_);
lean_ctor_set(v_reuseFailAlloc_4568_, 1, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4568_, 2, v_stop_4556_);
v___x_4564_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4565_ = lean_array_fget(v_array_4554_, v_start_4555_);
lean_dec(v_start_4555_);
lean_dec_ref(v_array_4554_);
v___x_4566_ = lean_array_push(v_acc_4552_, v___x_4565_);
v___x_4567_ = lean_apply_3(v_recur_4553_, v___x_4564_, v___x_4566_, lean_box(0));
return v___x_4567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4572_, lean_object* v_inst_4573_, lean_object* v_as_4574_){
_start:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4575_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4572_, v_as_4574_, v___x_4575_);
v___x_4577_ = lean_array_to_list(v___x_4576_);
v___x_4578_ = lean_box(0);
v___x_4579_ = l_List_mapTR_loop___redArg(v_inst_4573_, v___x_4577_, v___x_4578_);
v___x_4580_ = l_Lean_MessageData_ofList(v___x_4579_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4582_){
_start:
{
lean_object* v___f_4583_; lean_object* v___f_4584_; 
v___f_4583_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4584_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4584_, 0, v___f_4583_);
lean_closure_set(v___f_4584_, 1, v_inst_4582_);
return v___f_4584_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4585_, lean_object* v_inst_4586_){
_start:
{
lean_object* v___x_4587_; 
v___x_4587_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4586_);
return v___x_4587_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4591_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4592_ = l_Lean_MessageData_ofFormat(v___x_4591_);
return v___x_4592_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4596_ = l_Lean_MessageData_ofFormat(v___x_4595_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4597_, lean_object* v_x_4598_){
_start:
{
if (lean_obj_tag(v_x_4598_) == 0)
{
lean_object* v___x_4599_; 
lean_dec_ref(v_inst_4597_);
v___x_4599_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4599_;
}
else
{
lean_object* v_val_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_val_4600_ = lean_ctor_get(v_x_4598_, 0);
lean_inc(v_val_4600_);
lean_dec_ref_known(v_x_4598_, 1);
v___x_4601_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4602_ = lean_apply_1(v_inst_4597_, v_val_4600_);
v___x_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4601_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4603_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
return v___x_4605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4606_){
_start:
{
lean_object* v___f_4607_; 
v___f_4607_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4607_, 0, v_inst_4606_);
return v___f_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4608_, lean_object* v_inst_4609_){
_start:
{
lean_object* v___f_4610_; 
v___f_4610_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4610_, 0, v_inst_4609_);
return v___f_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4611_, lean_object* v_inst_4612_, lean_object* v_x_4613_){
_start:
{
lean_object* v_fst_4614_; lean_object* v_snd_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4629_; 
v_fst_4614_ = lean_ctor_get(v_x_4613_, 0);
v_snd_4615_ = lean_ctor_get(v_x_4613_, 1);
v_isSharedCheck_4629_ = !lean_is_exclusive(v_x_4613_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4617_ = v_x_4613_;
v_isShared_4618_ = v_isSharedCheck_4629_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_snd_4615_);
lean_inc(v_fst_4614_);
lean_dec(v_x_4613_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4629_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4622_; 
v___x_4619_ = lean_apply_1(v_inst_4611_, v_fst_4614_);
v___x_4620_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4618_ == 0)
{
lean_ctor_set_tag(v___x_4617_, 7);
lean_ctor_set(v___x_4617_, 1, v___x_4620_);
lean_ctor_set(v___x_4617_, 0, v___x_4619_);
v___x_4622_ = v___x_4617_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4619_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4623_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4622_);
lean_ctor_set(v___x_4624_, 1, v___x_4623_);
v___x_4625_ = lean_apply_1(v_inst_4612_, v_snd_4615_);
v___x_4626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4624_);
lean_ctor_set(v___x_4626_, 1, v___x_4625_);
v___x_4627_ = l_Lean_MessageData_paren(v___x_4626_);
return v___x_4627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4630_, lean_object* v_inst_4631_){
_start:
{
lean_object* v___f_4632_; 
v___f_4632_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4632_, 0, v_inst_4630_);
lean_closure_set(v___f_4632_, 1, v_inst_4631_);
return v___f_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4633_, lean_object* v_00_u03b2_4634_, lean_object* v_inst_4635_, lean_object* v_inst_4636_){
_start:
{
lean_object* v___f_4637_; 
v___f_4637_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4637_, 0, v_inst_4635_);
lean_closure_set(v___f_4637_, 1, v_inst_4636_);
return v___f_4637_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4642_ = l_Lean_MessageData_ofFormat(v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4643_){
_start:
{
if (lean_obj_tag(v_x_4643_) == 0)
{
lean_object* v___x_4644_; 
v___x_4644_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4644_;
}
else
{
lean_object* v_val_4645_; lean_object* v___x_4646_; 
v_val_4645_ = lean_ctor_get(v_x_4643_, 0);
lean_inc(v_val_4645_);
lean_dec_ref_known(v_x_4643_, 1);
v___x_4646_ = l_Lean_MessageData_ofExpr(v_val_4645_);
return v___x_4646_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4681_ = l_String_toRawSubstring_x27(v___x_4680_);
return v___x_4681_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4696_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4697_ = l_String_toRawSubstring_x27(v___x_4696_);
return v___x_4697_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v___x_4714_; uint8_t v___x_4715_; 
v___x_4714_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4711_);
v___x_4715_ = l_Lean_Syntax_isOfKind(v_x_4711_, v___x_4714_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
lean_dec(v_x_4711_);
v___x_4716_ = lean_box(1);
v___x_4717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
lean_ctor_set(v___x_4717_, 1, v_a_4713_);
return v___x_4717_;
}
else
{
lean_object* v_quotContext_4718_; lean_object* v_currMacroScope_4719_; lean_object* v_ref_4720_; lean_object* v___x_4721_; lean_object* v_interpStr_4722_; uint8_t v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v_quotContext_4718_ = lean_ctor_get(v_a_4712_, 1);
v_currMacroScope_4719_ = lean_ctor_get(v_a_4712_, 2);
v_ref_4720_ = lean_ctor_get(v_a_4712_, 5);
v___x_4721_ = lean_unsigned_to_nat(1u);
v_interpStr_4722_ = l_Lean_Syntax_getArg(v_x_4711_, v___x_4721_);
lean_dec(v_x_4711_);
v___x_4723_ = 0;
v___x_4724_ = l_Lean_SourceInfo_fromRef(v_ref_4720_, v___x_4723_);
v___x_4725_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4726_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4719_, 2);
lean_inc_n(v_quotContext_4718_, 2);
v___x_4727_ = l_Lean_addMacroScope(v_quotContext_4718_, v___x_4726_, v_currMacroScope_4719_);
v___x_4728_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4724_);
v___x_4729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4729_, 0, v___x_4724_);
lean_ctor_set(v___x_4729_, 1, v___x_4725_);
lean_ctor_set(v___x_4729_, 2, v___x_4727_);
lean_ctor_set(v___x_4729_, 3, v___x_4728_);
v___x_4730_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4731_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4732_ = l_Lean_addMacroScope(v_quotContext_4718_, v___x_4731_, v_currMacroScope_4719_);
v___x_4733_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4734_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4734_, 0, v___x_4724_);
lean_ctor_set(v___x_4734_, 1, v___x_4730_);
lean_ctor_set(v___x_4734_, 2, v___x_4732_);
lean_ctor_set(v___x_4734_, 3, v___x_4733_);
lean_inc_ref(v___x_4734_);
v___x_4735_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4722_, v___x_4729_, v___x_4734_, v___x_4734_, v_a_4712_, v_a_4713_);
lean_dec(v_interpStr_4722_);
if (lean_obj_tag(v___x_4735_) == 0)
{
lean_object* v_a_4736_; lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_a_4736_ = lean_ctor_get(v___x_4735_, 0);
v_a_4737_ = lean_ctor_get(v___x_4735_, 1);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4735_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_inc(v_a_4736_);
lean_dec(v___x_4735_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4736_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
}
else
{
lean_object* v_a_4745_; lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
v_a_4745_ = lean_ctor_get(v___x_4735_, 0);
v_a_4746_ = lean_ctor_get(v___x_4735_, 1);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4735_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4735_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_inc(v_a_4745_);
lean_dec(v___x_4735_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4745_);
lean_ctor_set(v_reuseFailAlloc_4752_, 1, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4754_, v_a_4755_, v_a_4756_);
lean_dec_ref(v_a_4755_);
return v_res_4757_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4760_ = l_Lean_stringToMessageData(v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4761_){
_start:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4762_ = lean_array_to_list(v_msgs_4761_);
v___x_4763_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4764_ = l_Lean_MessageData_joinSep(v___x_4762_, v___x_4763_);
v___x_4765_ = l_Lean_indentD(v___x_4764_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4766_, lean_object* v_lctx_4767_, lean_object* v_opts_4768_, lean_object* v_msg_4769_){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4770_ = l_Lean_Environment_ofKernelEnv(v_env_4766_);
v___x_4771_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4772_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4770_);
lean_ctor_set(v___x_4772_, 1, v___x_4771_);
lean_ctor_set(v___x_4772_, 2, v_lctx_4767_);
lean_ctor_set(v___x_4772_, 3, v_opts_4768_);
v___x_4773_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
lean_ctor_set(v___x_4773_, 1, v_msg_4769_);
return v___x_4773_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4776_ = l_Lean_stringToMessageData(v___x_4775_);
return v___x_4776_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4779_ = l_Lean_stringToMessageData(v___x_4778_);
return v___x_4779_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4782_ = l_Lean_stringToMessageData(v___x_4781_);
return v___x_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4783_, lean_object* v_n_4784_, lean_object* v_expectedType_4785_){
_start:
{
lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4786_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4787_ = l_Lean_MessageData_ofName(v_n_4784_);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4788_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l_Lean_indentExpr(v_givenType_4783_);
v___x_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4790_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v___x_4793_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4792_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l_Lean_indentExpr(v_expectedType_4785_);
v___x_4796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
return v___x_4796_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
return v___x_4798_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4799_ = lean_box(1);
v___x_4800_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4801_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4802_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
lean_ctor_set(v___x_4802_, 1, v___x_4800_);
lean_ctor_set(v___x_4802_, 2, v___x_4799_);
return v___x_4802_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_4804_; lean_object* v___x_4805_; 
v___x_4804_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__2));
v___x_4805_ = l_Lean_stringToMessageData(v___x_4804_);
return v___x_4805_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; 
v___x_4807_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__4));
v___x_4808_ = l_Lean_stringToMessageData(v___x_4807_);
return v___x_4808_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__6));
v___x_4811_ = l_Lean_stringToMessageData(v___x_4810_);
return v___x_4811_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4815_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__9));
v___x_4816_ = l_Lean_MessageData_ofFormat(v___x_4815_);
return v___x_4816_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__12(void){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4818_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__11));
v___x_4819_ = l_Lean_stringToMessageData(v___x_4818_);
return v___x_4819_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__14(void){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; 
v___x_4821_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__13));
v___x_4822_ = l_Lean_stringToMessageData(v___x_4821_);
return v___x_4822_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__16(void){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4824_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__15));
v___x_4825_ = l_Lean_stringToMessageData(v___x_4824_);
return v___x_4825_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__18(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__17));
v___x_4828_ = l_Lean_stringToMessageData(v___x_4827_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__20(void){
_start:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__19));
v___x_4831_ = l_Lean_stringToMessageData(v___x_4830_);
return v___x_4831_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__22(void){
_start:
{
lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4833_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__21));
v___x_4834_ = l_Lean_stringToMessageData(v___x_4833_);
return v___x_4834_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__24(void){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; 
v___x_4836_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__23));
v___x_4837_ = l_Lean_stringToMessageData(v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__26(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__25));
v___x_4840_ = l_Lean_stringToMessageData(v___x_4839_);
return v___x_4840_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__28(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__27));
v___x_4843_ = l_Lean_stringToMessageData(v___x_4842_);
return v___x_4843_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__30(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__29));
v___x_4846_ = l_Lean_stringToMessageData(v___x_4845_);
return v___x_4846_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__32(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__31));
v___x_4849_ = l_Lean_stringToMessageData(v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__34(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__33));
v___x_4852_ = l_Lean_stringToMessageData(v___x_4851_);
return v___x_4852_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__36(void){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__35));
v___x_4855_ = l_Lean_stringToMessageData(v___x_4854_);
return v___x_4855_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__38(void){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4857_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__37));
v___x_4858_ = l_Lean_stringToMessageData(v___x_4857_);
return v___x_4858_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__41(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__40));
v___x_4863_ = l_Lean_MessageData_ofFormat(v___x_4862_);
return v___x_4863_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__44(void){
_start:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; 
v___x_4867_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__43));
v___x_4868_ = l_Lean_MessageData_ofFormat(v___x_4867_);
return v___x_4868_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__47(void){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__46));
v___x_4873_ = l_Lean_MessageData_ofFormat(v___x_4872_);
return v___x_4873_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__50(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__49));
v___x_4878_ = l_Lean_MessageData_ofFormat(v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4879_, lean_object* v_opts_4880_){
_start:
{
switch(lean_obj_tag(v_e_4879_))
{
case 0:
{
lean_object* v_env_4881_; lean_object* v_name_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4895_; 
v_env_4881_ = lean_ctor_get(v_e_4879_, 0);
v_name_4882_ = lean_ctor_get(v_e_4879_, 1);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_e_4879_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4884_ = v_e_4879_;
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_name_4882_);
lean_inc(v_env_4881_);
lean_dec(v_e_4879_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4895_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4890_; 
v___x_4886_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4887_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__3, &l_Lean_Kernel_Exception_toMessageData___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__3);
v___x_4888_ = l_Lean_MessageData_ofName(v_name_4882_);
if (v_isShared_4885_ == 0)
{
lean_ctor_set_tag(v___x_4884_, 7);
lean_ctor_set(v___x_4884_, 1, v___x_4888_);
lean_ctor_set(v___x_4884_, 0, v___x_4887_);
v___x_4890_ = v___x_4884_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v___x_4888_);
v___x_4890_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4891_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4890_);
lean_ctor_set(v___x_4892_, 1, v___x_4891_);
v___x_4893_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4881_, v___x_4886_, v_opts_4880_, v___x_4892_);
return v___x_4893_;
}
}
}
case 1:
{
lean_object* v_env_4896_; lean_object* v_name_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4911_; 
v_env_4896_ = lean_ctor_get(v_e_4879_, 0);
v_name_4897_ = lean_ctor_get(v_e_4879_, 1);
v_isSharedCheck_4911_ = !lean_is_exclusive(v_e_4879_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4899_ = v_e_4879_;
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_name_4897_);
lean_inc(v_env_4896_);
lean_dec(v_e_4879_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4901_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4902_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__7, &l_Lean_Kernel_Exception_toMessageData___closed__7_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__7);
v___x_4903_ = 1;
v___x_4904_ = l_Lean_MessageData_ofConstName(v_name_4897_, v___x_4903_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set_tag(v___x_4899_, 7);
lean_ctor_set(v___x_4899_, 1, v___x_4904_);
lean_ctor_set(v___x_4899_, 0, v___x_4902_);
v___x_4906_ = v___x_4899_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4902_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v___x_4904_);
v___x_4906_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4907_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4906_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
v___x_4909_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4896_, v___x_4901_, v_opts_4880_, v___x_4908_);
return v___x_4909_;
}
}
}
case 2:
{
lean_object* v_env_4912_; lean_object* v_decl_4913_; lean_object* v_givenType_4914_; lean_object* v___x_4915_; 
v_env_4912_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4912_);
v_decl_4913_ = lean_ctor_get(v_e_4879_, 1);
lean_inc(v_decl_4913_);
v_givenType_4914_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_givenType_4914_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_4915_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
switch(lean_obj_tag(v_decl_4913_))
{
case 1:
{
lean_object* v_val_4916_; lean_object* v_toConstantVal_4917_; lean_object* v_name_4918_; lean_object* v_type_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_val_4916_ = lean_ctor_get(v_decl_4913_, 0);
lean_inc_ref(v_val_4916_);
lean_dec_ref_known(v_decl_4913_, 1);
v_toConstantVal_4917_ = lean_ctor_get(v_val_4916_, 0);
lean_inc_ref(v_toConstantVal_4917_);
lean_dec_ref(v_val_4916_);
v_name_4918_ = lean_ctor_get(v_toConstantVal_4917_, 0);
lean_inc(v_name_4918_);
v_type_4919_ = lean_ctor_get(v_toConstantVal_4917_, 2);
lean_inc_ref(v_type_4919_);
lean_dec_ref(v_toConstantVal_4917_);
v___x_4920_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4914_, v_name_4918_, v_type_4919_);
v___x_4921_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4912_, v___x_4915_, v_opts_4880_, v___x_4920_);
return v___x_4921_;
}
case 2:
{
lean_object* v_val_4922_; lean_object* v_toConstantVal_4923_; lean_object* v_name_4924_; lean_object* v_type_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_val_4922_ = lean_ctor_get(v_decl_4913_, 0);
lean_inc_ref(v_val_4922_);
lean_dec_ref_known(v_decl_4913_, 1);
v_toConstantVal_4923_ = lean_ctor_get(v_val_4922_, 0);
lean_inc_ref(v_toConstantVal_4923_);
lean_dec_ref(v_val_4922_);
v_name_4924_ = lean_ctor_get(v_toConstantVal_4923_, 0);
lean_inc(v_name_4924_);
v_type_4925_ = lean_ctor_get(v_toConstantVal_4923_, 2);
lean_inc_ref(v_type_4925_);
lean_dec_ref(v_toConstantVal_4923_);
v___x_4926_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4914_, v_name_4924_, v_type_4925_);
v___x_4927_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4912_, v___x_4915_, v_opts_4880_, v___x_4926_);
return v___x_4927_;
}
default: 
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_dec_ref(v_givenType_4914_);
lean_dec(v_decl_4913_);
v___x_4928_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__10, &l_Lean_Kernel_Exception_toMessageData___closed__10_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__10);
v___x_4929_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4912_, v___x_4915_, v_opts_4880_, v___x_4928_);
return v___x_4929_;
}
}
}
case 3:
{
lean_object* v_env_4930_; lean_object* v_name_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v_env_4930_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4930_);
v_name_4931_ = lean_ctor_get(v_e_4879_, 1);
lean_inc(v_name_4931_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_4932_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4933_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__12, &l_Lean_Kernel_Exception_toMessageData___closed__12_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__12);
v___x_4934_ = 1;
v___x_4935_ = l_Lean_MessageData_ofConstName(v_name_4931_, v___x_4934_);
v___x_4936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4933_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4930_, v___x_4932_, v_opts_4880_, v___x_4938_);
return v___x_4939_;
}
case 4:
{
lean_object* v_env_4940_; lean_object* v_name_4941_; lean_object* v_expr_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; uint8_t v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; 
v_env_4940_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4940_);
v_name_4941_ = lean_ctor_get(v_e_4879_, 1);
lean_inc(v_name_4941_);
v_expr_4942_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_expr_4942_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_4943_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4944_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__14, &l_Lean_Kernel_Exception_toMessageData___closed__14_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__14);
v___x_4945_ = 1;
v___x_4946_ = l_Lean_MessageData_ofConstName(v_name_4941_, v___x_4945_);
v___x_4947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4944_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__16, &l_Lean_Kernel_Exception_toMessageData___closed__16_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__16);
v___x_4949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4947_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = l_Lean_indentExpr(v_expr_4942_);
v___x_4951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4949_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
v___x_4952_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4940_, v___x_4943_, v_opts_4880_, v___x_4951_);
return v___x_4952_;
}
case 5:
{
lean_object* v_env_4953_; lean_object* v_lctx_4954_; lean_object* v_expr_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
v_env_4953_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4953_);
v_lctx_4954_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_4954_);
v_expr_4955_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_expr_4955_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_4956_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__18, &l_Lean_Kernel_Exception_toMessageData___closed__18_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__18);
v___x_4957_ = l_Lean_indentExpr(v_expr_4955_);
v___x_4958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4956_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4953_, v_lctx_4954_, v_opts_4880_, v___x_4958_);
return v___x_4959_;
}
case 6:
{
lean_object* v_env_4960_; lean_object* v_lctx_4961_; lean_object* v_expr_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v_env_4960_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4960_);
v_lctx_4961_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_4961_);
v_expr_4962_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_expr_4962_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_4963_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__20, &l_Lean_Kernel_Exception_toMessageData___closed__20_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__20);
v___x_4964_ = l_Lean_indentExpr(v_expr_4962_);
v___x_4965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4963_);
lean_ctor_set(v___x_4965_, 1, v___x_4964_);
v___x_4966_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4960_, v_lctx_4961_, v_opts_4880_, v___x_4965_);
return v___x_4966_;
}
case 7:
{
lean_object* v_env_4967_; lean_object* v_lctx_4968_; lean_object* v_name_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
v_env_4967_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4967_);
v_lctx_4968_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_4968_);
v_name_4969_ = lean_ctor_get(v_e_4879_, 2);
lean_inc(v_name_4969_);
lean_dec_ref_known(v_e_4879_, 5);
v___x_4970_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__22, &l_Lean_Kernel_Exception_toMessageData___closed__22_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__22);
v___x_4971_ = l_Lean_MessageData_ofName(v_name_4969_);
v___x_4972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4970_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
v___x_4973_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4972_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
v___x_4975_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4967_, v_lctx_4968_, v_opts_4880_, v___x_4974_);
return v___x_4975_;
}
case 8:
{
lean_object* v_env_4976_; lean_object* v_lctx_4977_; lean_object* v_expr_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_env_4976_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4976_);
v_lctx_4977_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_4977_);
v_expr_4978_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_expr_4978_);
lean_dec_ref_known(v_e_4879_, 4);
v___x_4979_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__24, &l_Lean_Kernel_Exception_toMessageData___closed__24_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__24);
v___x_4980_ = l_Lean_indentExpr(v_expr_4978_);
v___x_4981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4976_, v_lctx_4977_, v_opts_4880_, v___x_4981_);
return v___x_4982_;
}
case 9:
{
lean_object* v_env_4983_; lean_object* v_lctx_4984_; lean_object* v_app_4985_; lean_object* v_funType_4986_; lean_object* v_argType_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
v_env_4983_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_4983_);
v_lctx_4984_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_4984_);
v_app_4985_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_app_4985_);
v_funType_4986_ = lean_ctor_get(v_e_4879_, 3);
lean_inc_ref(v_funType_4986_);
v_argType_4987_ = lean_ctor_get(v_e_4879_, 4);
lean_inc_ref(v_argType_4987_);
lean_dec_ref_known(v_e_4879_, 5);
v___x_4988_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__26, &l_Lean_Kernel_Exception_toMessageData___closed__26_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__26);
v___x_4989_ = l_Lean_indentExpr(v_app_4985_);
v___x_4990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__28, &l_Lean_Kernel_Exception_toMessageData___closed__28_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__28);
v___x_4992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4990_);
lean_ctor_set(v___x_4992_, 1, v___x_4991_);
v___x_4993_ = l_Lean_indentExpr(v_argType_4987_);
v___x_4994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__30, &l_Lean_Kernel_Exception_toMessageData___closed__30_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__30);
v___x_4996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4996_, 0, v___x_4994_);
lean_ctor_set(v___x_4996_, 1, v___x_4995_);
v___x_4997_ = l_Lean_indentExpr(v_funType_4986_);
v___x_4998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4996_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4983_, v_lctx_4984_, v_opts_4880_, v___x_4998_);
return v___x_4999_;
}
case 10:
{
lean_object* v_env_5000_; lean_object* v_lctx_5001_; lean_object* v_proj_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v_env_5000_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_5000_);
v_lctx_5001_ = lean_ctor_get(v_e_4879_, 1);
lean_inc_ref(v_lctx_5001_);
v_proj_5002_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_proj_5002_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_5003_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__32, &l_Lean_Kernel_Exception_toMessageData___closed__32_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__32);
v___x_5004_ = l_Lean_indentExpr(v_proj_5002_);
v___x_5005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5003_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5000_, v_lctx_5001_, v_opts_4880_, v___x_5005_);
return v___x_5006_;
}
case 11:
{
lean_object* v_env_5007_; lean_object* v_name_5008_; lean_object* v_type_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; uint8_t v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v_env_5007_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_env_5007_);
v_name_5008_ = lean_ctor_get(v_e_4879_, 1);
lean_inc(v_name_5008_);
v_type_5009_ = lean_ctor_get(v_e_4879_, 2);
lean_inc_ref(v_type_5009_);
lean_dec_ref_known(v_e_4879_, 3);
v___x_5010_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_5011_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__34, &l_Lean_Kernel_Exception_toMessageData___closed__34_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__34);
v___x_5012_ = 1;
v___x_5013_ = l_Lean_MessageData_ofConstName(v_name_5008_, v___x_5012_);
v___x_5014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5014_, 0, v___x_5011_);
lean_ctor_set(v___x_5014_, 1, v___x_5013_);
v___x_5015_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__36, &l_Lean_Kernel_Exception_toMessageData___closed__36_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__36);
v___x_5016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5016_, 0, v___x_5014_);
lean_ctor_set(v___x_5016_, 1, v___x_5015_);
v___x_5017_ = l_Lean_indentExpr(v_type_5009_);
v___x_5018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5016_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
v___x_5019_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_5007_, v___x_5010_, v_opts_4880_, v___x_5018_);
return v___x_5019_;
}
case 12:
{
lean_object* v_msg_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
lean_dec_ref(v_opts_4880_);
v_msg_5020_ = lean_ctor_get(v_e_4879_, 0);
lean_inc_ref(v_msg_5020_);
lean_dec_ref_known(v_e_4879_, 1);
v___x_5021_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__38, &l_Lean_Kernel_Exception_toMessageData___closed__38_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__38);
v___x_5022_ = l_Lean_stringToMessageData(v_msg_5020_);
v___x_5023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5021_);
lean_ctor_set(v___x_5023_, 1, v___x_5022_);
return v___x_5023_;
}
case 13:
{
lean_object* v___x_5024_; 
lean_dec_ref(v_opts_4880_);
v___x_5024_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__41, &l_Lean_Kernel_Exception_toMessageData___closed__41_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__41);
return v___x_5024_;
}
case 14:
{
lean_object* v___x_5025_; 
lean_dec_ref(v_opts_4880_);
v___x_5025_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__44, &l_Lean_Kernel_Exception_toMessageData___closed__44_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__44);
return v___x_5025_;
}
case 15:
{
lean_object* v___x_5026_; 
lean_dec_ref(v_opts_4880_);
v___x_5026_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__47, &l_Lean_Kernel_Exception_toMessageData___closed__47_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__47);
return v___x_5026_;
}
default: 
{
lean_object* v___x_5027_; 
lean_dec_ref(v_opts_4880_);
v___x_5027_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__50, &l_Lean_Kernel_Exception_toMessageData___closed__50_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__50);
return v___x_5027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_5028_, lean_object* v_e_5029_, lean_object* v_cls_5030_){
_start:
{
lean_object* v___x_5031_; double v___x_5032_; uint8_t v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5031_ = lean_box(0);
v___x_5032_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_5033_ = 1;
v___x_5034_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_5035_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5035_, 0, v_cls_5030_);
lean_ctor_set(v___x_5035_, 1, v___x_5031_);
lean_ctor_set(v___x_5035_, 2, v___x_5034_);
lean_ctor_set_float(v___x_5035_, sizeof(void*)*3, v___x_5032_);
lean_ctor_set_float(v___x_5035_, sizeof(void*)*3 + 8, v___x_5032_);
lean_ctor_set_uint8(v___x_5035_, sizeof(void*)*3 + 16, v___x_5033_);
v___x_5036_ = lean_apply_1(v_inst_5028_, v_e_5029_);
v___x_5037_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_5038_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5035_);
lean_ctor_set(v___x_5038_, 1, v___x_5036_);
lean_ctor_set(v___x_5038_, 2, v___x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_5039_, lean_object* v_inst_5040_, lean_object* v_e_5041_, lean_object* v_cls_5042_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l_Lean_toTraceElem___redArg(v_inst_5040_, v_e_5041_, v_cls_5042_);
return v___x_5043_;
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
