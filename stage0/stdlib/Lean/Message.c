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
lean_object* v___x_1511_; lean_object* v___x_1578__overap_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_obj_once(&l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0, &l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0_once, _init_l_panic___at___00Lean_MessageData_formatAux_spec__3___closed__0);
v___x_1578__overap_1512_ = lean_panic_fn_borrowed(v___x_1511_, v_msg_1509_);
v___x_1513_ = lean_apply_1(v___x_1578__overap_1512_, lean_box(0));
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
static double _init_l_Lean_MessageData_formatAux___closed__9(void){
_start:
{
lean_object* v___x_1552_; double v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v___x_1553_ = lean_float_of_nat(v___x_1552_);
return v___x_1553_;
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
lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; double v___x_1657_; uint8_t v___x_1658_; 
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
v___x_1657_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_1658_ = lean_float_beq(v_startTime_1623_, v___x_1657_);
if (v___x_1658_ == 0)
{
goto v___jp_1649_;
}
else
{
if (v___x_1641_ == 0)
{
v_msg_1626_ = v___x_1648_;
goto v___jp_1625_;
}
else
{
goto v___jp_1649_;
}
}
v___jp_1649_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; double v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__8));
v___x_1651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1648_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_float_sub(v_stopTime_1624_, v_startTime_1623_);
v___x_1653_ = lean_float_to_string(v___x_1652_);
v___x_1654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1651_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
lean_ctor_set(v___x_1656_, 1, v___x_1647_);
v_msg_1626_ = v___x_1656_;
goto v___jp_1625_;
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_result_x3f_1622_);
lean_dec(v_cls_1621_);
lean_dec_ref(v_msg_1603_);
lean_dec(v_x_1558_);
lean_dec_ref(v_x_1557_);
v___x_1659_ = lean_array_to_list(v___x_1607_);
v___x_1660_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_1661_ = l_Std_Format_joinSep___at___00Lean_MessageData_formatAux_spec__2(v___x_1659_, v___x_1660_);
return v___x_1661_;
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
lean_object* v_f_1662_; lean_object* v___x_1663_; lean_object* v___y_1665_; 
v_f_1662_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_f_1662_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1663_ = ((lean_object*)(l_Lean_instImpl_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_box(0);
v___y_1665_ = v___x_1681_;
goto v___jp_1664_;
}
else
{
lean_object* v_val_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_val_1682_ = lean_ctor_get(v_x_1558_, 0);
v___x_1683_ = l_Lean_MessageData_mkPPContext(v_x_1557_, v_val_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___y_1665_ = v___x_1684_;
goto v___jp_1664_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_apply_2(v_f_1662_, v___y_1665_, lean_box(0));
v___x_1667_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v___x_1666_, v___x_1663_);
if (lean_obj_tag(v___x_1667_) == 1)
{
lean_object* v_val_1668_; 
lean_dec(v___x_1666_);
v_val_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v_x_1559_ = v_val_1668_;
goto _start;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v___x_1667_);
lean_dec(v_x_1558_);
lean_dec_ref(v_x_1557_);
v___x_1670_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__10));
v___x_1671_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__11));
v___x_1672_ = lean_unsigned_to_nat(409u);
v___x_1673_ = lean_unsigned_to_nat(8u);
v___x_1674_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__12));
v___x_1675_ = l___private_Init_Dynamic_0__Dynamic_typeNameImpl(v___x_1666_);
lean_dec(v___x_1666_);
v___x_1676_ = 1;
v___x_1677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1675_, v___x_1676_);
v___x_1678_ = lean_string_append(v___x_1674_, v___x_1677_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = l_mkPanicMessageWithDecl(v___x_1670_, v___x_1671_, v___x_1672_, v___x_1673_, v___x_1678_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = l_panic___at___00Lean_MessageData_formatAux_spec__3(v___x_1679_);
return v___x_1680_;
}
}
}
default: 
{
lean_object* v_a_1685_; 
v_a_1685_ = lean_ctor_get(v_x_1559_, 1);
lean_inc_ref(v_a_1685_);
lean_dec_ref(v_x_1559_);
v_x_1559_ = v_a_1685_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(lean_object* v_x_1687_, lean_object* v_x_1688_, size_t v_sz_1689_, size_t v_i_1690_, lean_object* v_bs_1691_){
_start:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
if (v___x_1693_ == 0)
{
lean_dec(v_x_1688_);
lean_dec_ref(v_x_1687_);
return v_bs_1691_;
}
else
{
lean_object* v_v_1694_; lean_object* v___x_1695_; lean_object* v_bs_x27_1696_; lean_object* v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
v_v_1694_ = lean_array_uget(v_bs_1691_, v_i_1690_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v_bs_x27_1696_ = lean_array_uset(v_bs_1691_, v_i_1690_, v___x_1695_);
lean_inc(v_x_1688_);
lean_inc_ref(v_x_1687_);
v___x_1697_ = l_Lean_MessageData_formatAux(v_x_1687_, v_x_1688_, v_v_1694_);
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1690_, v___x_1698_);
v___x_1700_ = lean_array_uset(v_bs_x27_1696_, v_i_1690_, v___x_1697_);
v_i_1690_ = v___x_1699_;
v_bs_1691_ = v___x_1700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1___boxed(lean_object* v_x_1702_, lean_object* v_x_1703_, lean_object* v_sz_1704_, lean_object* v_i_1705_, lean_object* v_bs_1706_, lean_object* v___y_1707_){
_start:
{
size_t v_sz_boxed_1708_; size_t v_i_boxed_1709_; lean_object* v_res_1710_; 
v_sz_boxed_1708_ = lean_unbox_usize(v_sz_1704_);
lean_dec(v_sz_1704_);
v_i_boxed_1709_ = lean_unbox_usize(v_i_1705_);
lean_dec(v_i_1705_);
v_res_1710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MessageData_formatAux_spec__1(v_x_1702_, v_x_1703_, v_sz_boxed_1708_, v_i_boxed_1709_, v_bs_1706_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_formatAux___boxed(lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_MessageData_formatAux(v_x_1711_, v_x_1712_, v_x_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format(lean_object* v_msgData_1719_, lean_object* v_ctx_x3f_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_MessageData_format___closed__0));
v___x_1723_ = l_Lean_MessageData_formatAux(v___x_1722_, v_ctx_x3f_1720_, v_msgData_1719_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_format___boxed(lean_object* v_msgData_1724_, lean_object* v_ctx_x3f_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lean_MessageData_format(v_msgData_1724_, v_ctx_x3f_1725_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString(lean_object* v_msgData_1728_){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1730_ = lean_box(0);
v___x_1731_ = l_Lean_MessageData_format(v_msgData_1728_, v___x_1730_);
v___x_1732_ = l_Std_Format_defWidth;
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = l_Std_Format_pretty(v___x_1731_, v___x_1732_, v___x_1733_, v___x_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_toString___boxed(lean_object* v_msgData_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_MessageData_toString(v_msgData_1735_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instAppend___lam__0(lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_a_1738_);
lean_ctor_set(v___x_1740_, 1, v_a_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeString___lam__0(lean_object* v_s_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_s_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeMVarId___lam__0(lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_a_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__1));
v___x_1768_ = l_Lean_MessageData_ofFormat(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeOptionExpr___lam__0(lean_object* v_o_1769_){
_start:
{
if (lean_obj_tag(v_o_1769_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; lean_object* v___x_1772_; 
v_val_1771_ = lean_ctor_get(v_o_1769_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v_o_1769_, 1);
v___x_1772_ = l_Lean_MessageData_ofExpr(v_val_1771_);
return v___x_1772_;
}
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__6));
v___x_1776_ = l_Lean_MessageData_ofFormat(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_MessageData_arrayExpr_toMessageData___closed__2));
v___x_1781_ = l_Lean_MessageData_ofFormat(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object* v_es_1782_, lean_object* v_i_1783_, lean_object* v_acc_1784_){
_start:
{
lean_object* v___y_1786_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_get_size(v_es_1782_);
v___x_1791_ = lean_nat_dec_lt(v_i_1783_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
lean_dec(v_i_1783_);
v___x_1792_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__0, &l_Lean_MessageData_arrayExpr_toMessageData___closed__0_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__0);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_acc_1784_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
return v___x_1793_;
}
else
{
lean_object* v_e_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_e_1794_ = lean_array_fget_borrowed(v_es_1782_, v_i_1783_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = lean_nat_dec_eq(v_i_1783_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_acc_1784_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
lean_inc(v_e_1794_);
v___x_1799_ = l_Lean_MessageData_ofExpr(v_e_1794_);
v___x_1800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1798_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
v___y_1786_ = v___x_1800_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_inc(v_e_1794_);
v___x_1801_ = l_Lean_MessageData_ofExpr(v_e_1794_);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v_acc_1784_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___y_1786_ = v___x_1802_;
goto v___jp_1785_;
}
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_i_1783_, v___x_1787_);
lean_dec(v_i_1783_);
v_i_1783_ = v___x_1788_;
v_acc_1784_ = v___y_1786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_arrayExpr_toMessageData___boxed(lean_object* v_es_1803_, lean_object* v_i_1804_, lean_object* v_acc_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1803_, v_i_1804_, v_acc_1805_);
lean_dec_ref(v_es_1803_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__1));
v___x_1811_ = l_Lean_MessageData_ofFormat(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0(lean_object* v_es_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_obj_once(&l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeArrayExpr___lam__0___closed__2);
v___x_1815_ = l_Lean_MessageData_arrayExpr_toMessageData(v_es_1812_, v___x_1813_, v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeArrayExpr___lam__0___boxed(lean_object* v_es_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_MessageData_instCoeArrayExpr___lam__0(v_es_1816_);
lean_dec_ref(v_es_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_bracket(lean_object* v_l_1820_, lean_object* v_f_1821_, lean_object* v_r_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1823_ = lean_string_length(v_l_1820_);
v___x_1824_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_l_1820_);
v___x_1825_ = l_Lean_MessageData_ofFormat(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v_f_1821_);
v___x_1827_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1827_, 0, v_r_1822_);
v___x_1828_ = l_Lean_MessageData_ofFormat(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1826_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1823_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_paren(lean_object* v_f_1832_){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__3));
v___x_1834_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__4));
v___x_1835_ = l_Lean_MessageData_bracket(v___x_1833_, v_f_1832_, v___x_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_sbracket(lean_object* v_f_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__3));
v___x_1838_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__5));
v___x_1839_ = l_Lean_MessageData_bracket(v___x_1837_, v_f_1836_, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_joinSep(lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v_x_1841_);
v___x_1842_ = lean_obj_once(&l_Lean_MessageData_nil___closed__0, &l_Lean_MessageData_nil___closed__0_once, _init_l_Lean_MessageData_nil___closed__0);
return v___x_1842_;
}
else
{
lean_object* v_tail_1843_; 
v_tail_1843_ = lean_ctor_get(v_x_1840_, 1);
if (lean_obj_tag(v_tail_1843_) == 0)
{
lean_object* v_head_1844_; 
lean_dec_ref(v_x_1841_);
v_head_1844_ = lean_ctor_get(v_x_1840_, 0);
lean_inc(v_head_1844_);
lean_dec_ref_known(v_x_1840_, 2);
return v_head_1844_;
}
else
{
lean_object* v_head_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
lean_inc(v_tail_1843_);
v_head_1845_ = lean_ctor_get(v_x_1840_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_x_1840_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_x_1840_, 1);
lean_dec(v_unused_1855_);
v___x_1847_ = v_x_1840_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_head_1845_);
lean_dec(v_x_1840_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
lean_inc_ref(v_x_1841_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set_tag(v___x_1847_, 7);
lean_ctor_set(v___x_1847_, 1, v_x_1841_);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_head_1845_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_x_1841_);
v___x_1850_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = l_Lean_MessageData_joinSep(v_tail_1843_, v_x_1841_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
return v___x_1852_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__2(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__1));
v___x_1860_ = l_Lean_MessageData_ofFormat(v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__5(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Lean_MessageData_ofList___closed__4));
v___x_1865_ = l_Lean_MessageData_ofFormat(v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__6(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_box(1);
v___x_1867_ = l_Lean_MessageData_ofFormat(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_MessageData_ofList___closed__7(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_1869_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___x_1868_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofList(lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__2, &l_Lean_MessageData_ofList___closed__2_once, _init_l_Lean_MessageData_ofList___closed__2);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__7, &l_Lean_MessageData_ofList___closed__7_once, _init_l_Lean_MessageData_ofList___closed__7);
v___x_1874_ = l_Lean_MessageData_joinSep(v_x_1871_, v___x_1873_);
v___x_1875_ = l_Lean_MessageData_sbracket(v___x_1874_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofArray(lean_object* v_msgs_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_array_to_list(v_msgs_1876_);
v___x_1878_ = l_Lean_MessageData_ofList(v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__2(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_Lean_MessageData_orList___closed__1));
v___x_1883_ = l_Lean_MessageData_ofFormat(v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__5(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = ((lean_object*)(l_Lean_MessageData_orList___closed__4));
v___x_1888_ = l_Lean_MessageData_ofFormat(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l_Lean_MessageData_orList___closed__8(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_MessageData_orList___closed__7));
v___x_1893_ = l_Lean_MessageData_ofFormat(v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_orList(lean_object* v_xs_1894_){
_start:
{
if (lean_obj_tag(v_xs_1894_) == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1895_;
}
else
{
lean_object* v_tail_1896_; 
v_tail_1896_ = lean_ctor_get(v_xs_1894_, 1);
lean_inc(v_tail_1896_);
if (lean_obj_tag(v_tail_1896_) == 0)
{
lean_object* v_head_1897_; 
v_head_1897_ = lean_ctor_get(v_xs_1894_, 0);
lean_inc(v_head_1897_);
lean_dec_ref_known(v_xs_1894_, 2);
return v_head_1897_;
}
else
{
lean_object* v_tail_1898_; 
v_tail_1898_ = lean_ctor_get(v_tail_1896_, 1);
if (lean_obj_tag(v_tail_1898_) == 0)
{
lean_object* v_head_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1916_; 
v_head_1899_ = lean_ctor_get(v_xs_1894_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_xs_1894_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_xs_1894_, 1);
lean_dec(v_unused_1917_);
v___x_1901_ = v_xs_1894_;
v_isShared_1902_ = v_isSharedCheck_1916_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_head_1899_);
lean_dec(v_xs_1894_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1916_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_head_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1914_; 
v_head_1903_ = lean_ctor_get(v_tail_1896_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_tail_1896_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_tail_1896_, 1);
lean_dec(v_unused_1915_);
v___x_1905_ = v_tail_1896_;
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_head_1903_);
lean_dec(v_tail_1896_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1914_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_obj_once(&l_Lean_MessageData_orList___closed__5, &l_Lean_MessageData_orList___closed__5_once, _init_l_Lean_MessageData_orList___closed__5);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 7);
lean_ctor_set(v___x_1905_, 1, v___x_1907_);
lean_ctor_set(v___x_1905_, 0, v_head_1899_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_head_1899_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 7);
lean_ctor_set(v___x_1901_, 1, v_head_1903_);
lean_ctor_set(v___x_1901_, 0, v___x_1909_);
v___x_1911_ = v___x_1901_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_head_1903_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1941_; 
v_isSharedCheck_1941_ = !lean_is_exclusive(v_tail_1896_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; lean_object* v_unused_1943_; 
v_unused_1942_ = lean_ctor_get(v_tail_1896_, 1);
lean_dec(v_unused_1942_);
v_unused_1943_ = lean_ctor_get(v_tail_1896_, 0);
lean_dec(v_unused_1943_);
v___x_1919_ = v_tail_1896_;
v_isShared_1920_ = v_isSharedCheck_1941_;
goto v_resetjp_1918_;
}
else
{
lean_dec(v_tail_1896_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1941_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1921_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1894_);
v___x_1922_ = lean_array_mk(v_xs_1894_);
v___x_1923_ = lean_array_pop(v___x_1922_);
v___x_1924_ = lean_array_to_list(v___x_1923_);
v___x_1925_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1926_ = l_Lean_MessageData_joinSep(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_obj_once(&l_Lean_MessageData_orList___closed__8, &l_Lean_MessageData_orList___closed__8_once, _init_l_Lean_MessageData_orList___closed__8);
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 7);
lean_ctor_set(v___x_1919_, 1, v___x_1927_);
lean_ctor_set(v___x_1919_, 0, v___x_1926_);
v___x_1929_ = v___x_1919_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v___x_1930_ = l_List_getLast_x21___redArg(v___x_1921_, v_xs_1894_);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_xs_1894_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; lean_object* v_unused_1939_; 
v_unused_1938_ = lean_ctor_get(v_xs_1894_, 1);
lean_dec(v_unused_1938_);
v_unused_1939_ = lean_ctor_get(v_xs_1894_, 0);
lean_dec(v_unused_1939_);
v___x_1932_ = v_xs_1894_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_dec(v_xs_1894_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set_tag(v___x_1932_, 7);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
lean_ctor_set(v___x_1932_, 0, v___x_1929_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
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
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = ((lean_object*)(l_Lean_MessageData_andList___closed__1));
v___x_1948_ = l_Lean_MessageData_ofFormat(v___x_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lean_MessageData_andList___closed__5(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = ((lean_object*)(l_Lean_MessageData_andList___closed__4));
v___x_1953_ = l_Lean_MessageData_ofFormat(v___x_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_andList(lean_object* v_xs_1954_){
_start:
{
if (lean_obj_tag(v_xs_1954_) == 0)
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_obj_once(&l_Lean_MessageData_orList___closed__2, &l_Lean_MessageData_orList___closed__2_once, _init_l_Lean_MessageData_orList___closed__2);
return v___x_1955_;
}
else
{
lean_object* v_tail_1956_; 
v_tail_1956_ = lean_ctor_get(v_xs_1954_, 1);
lean_inc(v_tail_1956_);
if (lean_obj_tag(v_tail_1956_) == 0)
{
lean_object* v_head_1957_; 
v_head_1957_ = lean_ctor_get(v_xs_1954_, 0);
lean_inc(v_head_1957_);
lean_dec_ref_known(v_xs_1954_, 2);
return v_head_1957_;
}
else
{
lean_object* v_tail_1958_; 
v_tail_1958_ = lean_ctor_get(v_tail_1956_, 1);
if (lean_obj_tag(v_tail_1958_) == 0)
{
lean_object* v_head_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1976_; 
v_head_1959_ = lean_ctor_get(v_xs_1954_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_xs_1954_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v_xs_1954_, 1);
lean_dec(v_unused_1977_);
v___x_1961_ = v_xs_1954_;
v_isShared_1962_ = v_isSharedCheck_1976_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_head_1959_);
lean_dec(v_xs_1954_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1976_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_head_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1974_; 
v_head_1963_ = lean_ctor_get(v_tail_1956_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_tail_1956_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_tail_1956_, 1);
lean_dec(v_unused_1975_);
v___x_1965_ = v_tail_1956_;
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_head_1963_);
lean_dec(v_tail_1956_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1974_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_obj_once(&l_Lean_MessageData_andList___closed__2, &l_Lean_MessageData_andList___closed__2_once, _init_l_Lean_MessageData_andList___closed__2);
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 7);
lean_ctor_set(v___x_1965_, 1, v___x_1967_);
lean_ctor_set(v___x_1965_, 0, v_head_1959_);
v___x_1969_ = v___x_1965_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_head_1959_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 7);
lean_ctor_set(v___x_1961_, 1, v_head_1963_);
lean_ctor_set(v___x_1961_, 0, v___x_1969_);
v___x_1971_ = v___x_1961_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_head_1963_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2001_; 
v_isSharedCheck_2001_ = !lean_is_exclusive(v_tail_1956_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; lean_object* v_unused_2003_; 
v_unused_2002_ = lean_ctor_get(v_tail_1956_, 1);
lean_dec(v_unused_2002_);
v_unused_2003_ = lean_ctor_get(v_tail_1956_, 0);
lean_dec(v_unused_2003_);
v___x_1979_ = v_tail_1956_;
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_tail_1956_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2001_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1981_ = ((lean_object*)(l_Lean_instInhabitedMessageData_default));
lean_inc_ref(v_xs_1954_);
v___x_1982_ = lean_array_mk(v_xs_1954_);
v___x_1983_ = lean_array_pop(v___x_1982_);
v___x_1984_ = lean_array_to_list(v___x_1983_);
v___x_1985_ = lean_obj_once(&l_Lean_MessageData_arrayExpr_toMessageData___closed__3, &l_Lean_MessageData_arrayExpr_toMessageData___closed__3_once, _init_l_Lean_MessageData_arrayExpr_toMessageData___closed__3);
v___x_1986_ = l_Lean_MessageData_joinSep(v___x_1984_, v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Lean_MessageData_andList___closed__5, &l_Lean_MessageData_andList___closed__5_once, _init_l_Lean_MessageData_andList___closed__5);
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 7);
lean_ctor_set(v___x_1979_, 1, v___x_1987_);
lean_ctor_set(v___x_1979_, 0, v___x_1986_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v___x_1990_ = l_List_getLast_x21___redArg(v___x_1981_, v_xs_1954_);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_xs_1954_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; 
v_unused_1998_ = lean_ctor_get(v_xs_1954_, 1);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_xs_1954_, 0);
lean_dec(v_unused_1999_);
v___x_1992_ = v_xs_1954_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_dec(v_xs_1954_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 7);
lean_ctor_set(v___x_1992_, 1, v___x_1990_);
lean_ctor_set(v___x_1992_, 0, v___x_1989_);
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
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
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__3(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_MessageData_note___closed__2));
v___x_2010_ = l_Lean_MessageData_ofFormat(v___x_2009_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_MessageData_note___closed__4(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = lean_obj_once(&l_Lean_MessageData_note___closed__3, &l_Lean_MessageData_note___closed__3_once, _init_l_Lean_MessageData_note___closed__3);
v___x_2012_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_note(lean_object* v_note_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_obj_once(&l_Lean_MessageData_note___closed__4, &l_Lean_MessageData_note___closed__4_once, _init_l_Lean_MessageData_note___closed__4);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v_note_2014_);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__2(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_MessageData_hint_x27___closed__1));
v___x_2021_ = l_Lean_MessageData_ofFormat(v___x_2020_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lean_MessageData_hint_x27___closed__3(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__2, &l_Lean_MessageData_hint_x27___closed__2_once, _init_l_Lean_MessageData_hint_x27___closed__2);
v___x_2023_ = lean_obj_once(&l_Lean_MessageData_note___closed__0, &l_Lean_MessageData_note___closed__0_once, _init_l_Lean_MessageData_note___closed__0);
v___x_2024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
lean_ctor_set(v___x_2024_, 1, v___x_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint_x27(lean_object* v_hint_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_obj_once(&l_Lean_MessageData_hint_x27___closed__3, &l_Lean_MessageData_hint_x27___closed__3_once, _init_l_Lean_MessageData_hint_x27___closed__3);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v_hint_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_instCoeListExpr___lam__0(lean_object* v_es_2030_){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = ((lean_object*)(l_Lean_MessageData_instCoeExpr___closed__0));
v___x_2032_ = lean_box(0);
v___x_2033_ = l_List_mapTR_loop___redArg(v___x_2031_, v_es_2030_, v___x_2032_);
v___x_2034_ = l_Lean_MessageData_ofList(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default___redArg(lean_object* v_inst_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; 
v___x_2038_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_2039_ = l_Lean_instInhabitedPosition_default;
v___x_2040_ = lean_box(0);
v___x_2041_ = 0;
v___x_2042_ = 2;
v___x_2043_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2043_, 0, v___x_2038_);
lean_ctor_set(v___x_2043_, 1, v___x_2039_);
lean_ctor_set(v___x_2043_, 2, v___x_2040_);
lean_ctor_set(v___x_2043_, 3, v___x_2038_);
lean_ctor_set(v___x_2043_, 4, v_inst_2037_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*5, v___x_2041_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*5 + 1, v___x_2042_);
lean_ctor_set_uint8(v___x_2043_, sizeof(void*)*5 + 2, v___x_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage_default(lean_object* v_00_u03b1_2044_, lean_object* v_inst_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage___redArg(lean_object* v_inst_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBaseMessage(lean_object* v_a_2049_, lean_object* v_inst_2050_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_instInhabitedBaseMessage_default___redArg(v_inst_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson___redArg(lean_object* v_inst_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v_fileName_2066_; lean_object* v_pos_2067_; lean_object* v_endPos_2068_; uint8_t v_keepFullRange_2069_; uint8_t v_severity_2070_; uint8_t v_isSilent_2071_; lean_object* v_caption_2072_; lean_object* v_data_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_fileName_2066_ = lean_ctor_get(v_x_2065_, 0);
lean_inc_ref(v_fileName_2066_);
v_pos_2067_ = lean_ctor_get(v_x_2065_, 1);
lean_inc_ref(v_pos_2067_);
v_endPos_2068_ = lean_ctor_get(v_x_2065_, 2);
lean_inc(v_endPos_2068_);
v_keepFullRange_2069_ = lean_ctor_get_uint8(v_x_2065_, sizeof(void*)*5);
v_severity_2070_ = lean_ctor_get_uint8(v_x_2065_, sizeof(void*)*5 + 1);
v_isSilent_2071_ = lean_ctor_get_uint8(v_x_2065_, sizeof(void*)*5 + 2);
v_caption_2072_ = lean_ctor_get(v_x_2065_, 3);
lean_inc_ref(v_caption_2072_);
v_data_2073_ = lean_ctor_get(v_x_2065_, 4);
lean_inc(v_data_2073_);
lean_dec_ref(v_x_2065_);
v___x_2074_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__0));
v___x_2075_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2076_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_fileName_2066_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2081_ = l_Lean_instToJsonPosition_toJson(v_pos_2067_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2078_);
v___x_2084_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2085_ = l_Lean_Option_toJson___redArg(v___x_2074_, v_endPos_2068_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2078_);
v___x_2088_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2089_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2089_, 0, v_keepFullRange_2069_);
v___x_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2088_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2078_);
v___x_2092_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2093_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2070_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v___x_2078_);
v___x_2096_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2097_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2097_, 0, v_isSilent_2071_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2096_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2078_);
v___x_2100_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_caption_2072_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2078_);
v___x_2104_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2105_ = lean_apply_1(v_inst_2064_, v_data_2073_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v___x_2078_);
v___x_2108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___x_2078_);
v___x_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2103_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2099_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2095_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2091_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2087_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2083_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2079_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__9));
v___x_2117_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2118_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(lean_box(0), lean_box(0), v___x_2116_, v___x_2115_, v___x_2117_);
v___x_2119_ = l_Lean_Json_mkObj(v___x_2118_);
lean_dec(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage_toJson(lean_object* v_00_u03b1_2120_, lean_object* v_inst_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_instToJsonBaseMessage_toJson___redArg(v_inst_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage___redArg(lean_object* v_inst_2124_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2125_, 0, lean_box(0));
lean_closure_set(v___x_2125_, 1, v_inst_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonBaseMessage(lean_object* v_00_u03b1_2126_, lean_object* v_inst_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_closure((void*)(l_Lean_instToJsonBaseMessage_toJson), 3, 2);
lean_closure_set(v___x_2128_, 0, lean_box(0));
lean_closure_set(v___x_2128_, 1, v_inst_2127_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3(void){
_start:
{
uint8_t v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = 1;
v___x_2135_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__2));
v___x_2136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2135_, v___x_2134_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2139_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__3);
v___x_2140_ = lean_string_append(v___x_2139_, v___x_2138_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7(void){
_start:
{
uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = 1;
v___x_2144_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__6));
v___x_2145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2147_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2148_ = lean_string_append(v___x_2147_, v___x_2146_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2151_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__8);
v___x_2152_ = lean_string_append(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14(void){
_start:
{
uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = 1;
v___x_2159_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__13));
v___x_2160_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2159_, v___x_2158_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2162_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2163_ = lean_string_append(v___x_2162_, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2165_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__15);
v___x_2166_ = lean_string_append(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18(void){
_start:
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = 1;
v___x_2170_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__17));
v___x_2171_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2170_, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2173_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2174_ = lean_string_append(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2176_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__19);
v___x_2177_ = lean_string_append(v___x_2176_, v___x_2175_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23(void){
_start:
{
uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2181_ = 1;
v___x_2182_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__22));
v___x_2183_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2182_, v___x_2181_);
return v___x_2183_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2185_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2186_ = lean_string_append(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2188_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__24);
v___x_2189_ = lean_string_append(v___x_2188_, v___x_2187_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27(void){
_start:
{
uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = 1;
v___x_2193_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__26));
v___x_2194_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2196_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2197_ = lean_string_append(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2199_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__28);
v___x_2200_ = lean_string_append(v___x_2199_, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31(void){
_start:
{
uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = 1;
v___x_2204_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__30));
v___x_2205_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2207_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2208_ = lean_string_append(v___x_2207_, v___x_2206_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2210_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__32);
v___x_2211_ = lean_string_append(v___x_2210_, v___x_2209_);
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35(void){
_start:
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = 1;
v___x_2215_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__34));
v___x_2216_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2218_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2219_ = lean_string_append(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2221_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__36);
v___x_2222_ = lean_string_append(v___x_2221_, v___x_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39(void){
_start:
{
uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = 1;
v___x_2226_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__38));
v___x_2227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2229_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__5);
v___x_2230_ = lean_string_append(v___x_2229_, v___x_2228_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2232_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__40);
v___x_2233_ = lean_string_append(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson___redArg(lean_object* v_inst_2234_, lean_object* v_json_2235_){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__0));
v___x_2237_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2235_);
v___x_2238_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2236_, v___x_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2248_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2243_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__10);
v___x_2244_ = lean_string_append(v___x_2243_, v_a_2239_);
lean_dec(v_a_2239_);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2244_);
v___x_2246_ = v___x_2241_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2249_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2238_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2238_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 0);
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
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
lean_object* v_a_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_a_2257_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2258_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__11));
v___x_2259_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__12));
v___x_2260_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2235_);
v___x_2261_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2258_, v___x_2260_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
v___x_2266_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__16);
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
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
lean_object* v_a_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2281_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2235_);
v___x_2282_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2259_, v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2292_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2292_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__20);
v___x_2288_ = lean_string_append(v___x_2287_, v_a_2283_);
lean_dec(v_a_2283_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2288_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
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
else
{
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2293_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2282_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2282_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set_tag(v___x_2295_, 0);
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
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
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v_a_2301_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2282_, 1);
v___x_2302_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__21));
v___x_2303_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2235_);
v___x_2304_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2302_, v___x_2303_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
v___x_2309_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__25);
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
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2323_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2324_ = ((lean_object*)(l_Lean_instFromJsonMessageSeverity___closed__0));
v___x_2325_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2235_);
v___x_2326_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2324_, v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2336_; 
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2336_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__29);
v___x_2332_ = lean_string_append(v___x_2331_, v_a_2327_);
lean_dec(v_a_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2332_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
else
{
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2337_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2326_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2326_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
lean_ctor_set_tag(v___x_2339_, 0);
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
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
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2345_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2346_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2235_);
v___x_2347_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2302_, v___x_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2357_; 
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
v___x_2352_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__33);
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
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_a_2366_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2367_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2235_);
v___x_2368_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v___x_2236_, v___x_2367_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2378_; 
lean_dec(v_a_2366_);
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
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
v___x_2373_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__37);
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
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_a_2366_);
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
lean_dec(v_json_2235_);
lean_dec_ref(v_inst_2234_);
v_a_2379_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2368_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2368_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set_tag(v___x_2381_, 0);
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
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
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2387_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2388_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2389_ = l_Lean_Json_getObjValAs_x3f___redArg(v_json_2235_, v_inst_2234_, v___x_2388_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_a_2387_);
lean_dec(v_a_2366_);
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2399_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2399_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2394_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__41);
v___x_2395_ = lean_string_append(v___x_2394_, v_a_2390_);
lean_dec(v_a_2390_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2395_);
v___x_2397_ = v___x_2392_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
else
{
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_a_2387_);
lean_dec(v_a_2366_);
lean_dec(v_a_2345_);
lean_dec(v_a_2323_);
lean_dec(v_a_2301_);
lean_dec(v_a_2280_);
lean_dec(v_a_2257_);
v_a_2400_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2389_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2389_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
lean_ctor_set_tag(v___x_2402_, 0);
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
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
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_a_2408_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v___x_2389_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2389_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; uint8_t v___x_2413_; uint8_t v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2417_; 
v___x_2412_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2412_, 0, v_a_2257_);
lean_ctor_set(v___x_2412_, 1, v_a_2280_);
lean_ctor_set(v___x_2412_, 2, v_a_2301_);
lean_ctor_set(v___x_2412_, 3, v_a_2387_);
lean_ctor_set(v___x_2412_, 4, v_a_2408_);
v___x_2413_ = lean_unbox(v_a_2323_);
lean_dec(v_a_2323_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*5, v___x_2413_);
v___x_2414_ = lean_unbox(v_a_2345_);
lean_dec(v_a_2345_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*5 + 1, v___x_2414_);
v___x_2415_ = lean_unbox(v_a_2366_);
lean_dec(v_a_2366_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*5 + 2, v___x_2415_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2417_ = v___x_2410_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
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
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage_fromJson(lean_object* v_00_u03b1_2420_, lean_object* v_inst_2421_, lean_object* v_json_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_instFromJsonBaseMessage_fromJson___redArg(v_inst_2421_, v_json_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage___redArg(lean_object* v_inst_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2425_, 0, lean_box(0));
lean_closure_set(v___x_2425_, 1, v_inst_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonBaseMessage(lean_object* v_00_u03b1_2426_, lean_object* v_inst_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_closure((void*)(l_Lean_instFromJsonBaseMessage_fromJson), 3, 2);
lean_closure_set(v___x_2428_, 0, lean_box(0));
lean_closure_set(v___x_2428_, 1, v_inst_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 0)
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_box(0);
return v___x_2430_;
}
else
{
lean_object* v_val_2431_; lean_object* v___x_2432_; 
v_val_2431_ = lean_ctor_get(v_x_2429_, 0);
lean_inc(v_val_2431_);
lean_dec_ref_known(v_x_2429_, 1);
v___x_2432_ = l_Lean_instToJsonPosition_toJson(v_val_2431_);
return v___x_2432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
if (lean_obj_tag(v_a_2433_) == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_array_to_list(v_a_2434_);
return v___x_2435_;
}
else
{
lean_object* v_head_2436_; lean_object* v_tail_2437_; lean_object* v___x_2438_; 
v_head_2436_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_head_2436_);
v_tail_2437_ = lean_ctor_get(v_a_2433_, 1);
lean_inc(v_tail_2437_);
lean_dec_ref_known(v_a_2433_, 2);
v___x_2438_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_2434_, v_head_2436_);
v_a_2433_ = v_tail_2437_;
v_a_2434_ = v___x_2438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToJsonSerialMessage_toJson(lean_object* v_x_2441_){
_start:
{
lean_object* v_toBaseMessage_2442_; lean_object* v_kind_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2508_; 
v_toBaseMessage_2442_ = lean_ctor_get(v_x_2441_, 0);
v_kind_2443_ = lean_ctor_get(v_x_2441_, 1);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_x_2441_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2445_ = v_x_2441_;
v_isShared_2446_ = v_isSharedCheck_2508_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_kind_2443_);
lean_inc(v_toBaseMessage_2442_);
lean_dec(v_x_2441_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2508_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_fileName_2447_; lean_object* v_pos_2448_; lean_object* v_endPos_2449_; uint8_t v_keepFullRange_2450_; uint8_t v_severity_2451_; uint8_t v_isSilent_2452_; lean_object* v_caption_2453_; lean_object* v_data_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2458_; 
v_fileName_2447_ = lean_ctor_get(v_toBaseMessage_2442_, 0);
lean_inc_ref(v_fileName_2447_);
v_pos_2448_ = lean_ctor_get(v_toBaseMessage_2442_, 1);
lean_inc_ref(v_pos_2448_);
v_endPos_2449_ = lean_ctor_get(v_toBaseMessage_2442_, 2);
lean_inc(v_endPos_2449_);
v_keepFullRange_2450_ = lean_ctor_get_uint8(v_toBaseMessage_2442_, sizeof(void*)*5);
v_severity_2451_ = lean_ctor_get_uint8(v_toBaseMessage_2442_, sizeof(void*)*5 + 1);
v_isSilent_2452_ = lean_ctor_get_uint8(v_toBaseMessage_2442_, sizeof(void*)*5 + 2);
v_caption_2453_ = lean_ctor_get(v_toBaseMessage_2442_, 3);
lean_inc_ref(v_caption_2453_);
v_data_2454_ = lean_ctor_get(v_toBaseMessage_2442_, 4);
lean_inc(v_data_2454_);
lean_dec_ref(v_toBaseMessage_2442_);
v___x_2455_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_2456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_fileName_2447_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 1, v___x_2456_);
lean_ctor_set(v___x_2445_, 0, v___x_2455_);
v___x_2458_ = v___x_2445_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_2462_ = l_Lean_instToJsonPosition_toJson(v_pos_2448_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2459_);
v___x_2465_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_2466_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_2449_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v___x_2459_);
v___x_2469_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_2470_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2470_, 0, v_keepFullRange_2450_);
v___x_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2469_);
lean_ctor_set(v___x_2471_, 1, v___x_2470_);
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v___x_2459_);
v___x_2473_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_2474_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_2451_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2459_);
v___x_2477_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_2478_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2478_, 0, v_isSilent_2452_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2459_);
v___x_2481_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_2482_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_caption_2453_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___x_2459_);
v___x_2485_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_2486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2486_, 0, v_data_2454_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2487_);
lean_ctor_set(v___x_2488_, 1, v___x_2459_);
v___x_2489_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2490_ = 1;
v___x_2491_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2443_, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2489_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2459_);
v___x_2495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2459_);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2488_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2484_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2480_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2476_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2472_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2468_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2464_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2460_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_2505_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_2503_, v___x_2504_);
v___x_2506_ = l_Lean_Json_mkObj(v___x_2505_);
lean_dec(v___x_2505_);
return v___x_2506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(lean_object* v_j_2511_, lean_object* v_k_2512_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = l_Lean_Json_getObjValD(v_j_2511_, v_k_2512_);
v___x_2514_ = l_Lean_Json_getStr_x3f(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0___boxed(lean_object* v_j_2515_, lean_object* v_k_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_j_2515_, v_k_2516_);
lean_dec_ref(v_k_2516_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(lean_object* v_j_2518_, lean_object* v_k_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = l_Lean_Json_getObjValD(v_j_2518_, v_k_2519_);
v___x_2521_ = l_Lean_instFromJsonPosition_fromJson(v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1___boxed(lean_object* v_j_2522_, lean_object* v_k_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_j_2522_, v_k_2523_);
lean_dec_ref(v_k_2523_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(lean_object* v_j_2525_, lean_object* v_k_2526_){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = l_Lean_Json_getObjValD(v_j_2525_, v_k_2526_);
v___x_2528_ = l_Lean_Json_getBool_x3f(v___x_2527_);
lean_dec(v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3___boxed(lean_object* v_j_2529_, lean_object* v_k_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_j_2529_, v_k_2530_);
lean_dec_ref(v_k_2530_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(lean_object* v_j_2532_, lean_object* v_k_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = l_Lean_Json_getObjValD(v_j_2532_, v_k_2533_);
v___x_2535_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4___boxed(lean_object* v_j_2536_, lean_object* v_k_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_j_2536_, v_k_2537_);
lean_dec_ref(v_k_2537_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(lean_object* v_j_2539_, lean_object* v_k_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = l_Lean_Json_getObjValD(v_j_2539_, v_k_2540_);
v___x_2542_ = l_Lean_Name_fromJson_x3f(v___x_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5___boxed(lean_object* v_j_2543_, lean_object* v_k_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_j_2543_, v_k_2544_);
lean_dec_ref(v_k_2544_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(lean_object* v_x_2548_){
_start:
{
if (lean_obj_tag(v_x_2548_) == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2___closed__0));
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Lean_instFromJsonPosition_fromJson(v_x_2548_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2567_; 
v_a_2559_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2561_ = v___x_2550_;
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2550_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2567_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v_a_2559_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2563_);
v___x_2565_ = v___x_2561_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(lean_object* v_j_2568_, lean_object* v_k_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = l_Lean_Json_getObjValD(v_j_2568_, v_k_2569_);
v___x_2571_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2_spec__2(v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2___boxed(lean_object* v_j_2572_, lean_object* v_k_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_j_2572_, v_k_2573_);
lean_dec_ref(v_k_2573_);
return v_res_2574_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = 1;
v___x_2580_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__1));
v___x_2581_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__4));
v___x_2583_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__2, &l_Lean_instFromJsonSerialMessage_fromJson___closed__2_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__2);
v___x_2584_ = lean_string_append(v___x_2583_, v___x_2582_);
return v___x_2584_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__7);
v___x_2586_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2587_ = lean_string_append(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2589_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__4, &l_Lean_instFromJsonSerialMessage_fromJson___closed__4_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__4);
v___x_2590_ = lean_string_append(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__14);
v___x_2592_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2593_ = lean_string_append(v___x_2592_, v___x_2591_);
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2595_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__6, &l_Lean_instFromJsonSerialMessage_fromJson___closed__6_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__6);
v___x_2596_ = lean_string_append(v___x_2595_, v___x_2594_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__18);
v___x_2598_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2599_ = lean_string_append(v___x_2598_, v___x_2597_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2601_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__8, &l_Lean_instFromJsonSerialMessage_fromJson___closed__8_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__8);
v___x_2602_ = lean_string_append(v___x_2601_, v___x_2600_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__23);
v___x_2604_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2605_ = lean_string_append(v___x_2604_, v___x_2603_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2607_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__10, &l_Lean_instFromJsonSerialMessage_fromJson___closed__10_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__10);
v___x_2608_ = lean_string_append(v___x_2607_, v___x_2606_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__27);
v___x_2610_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2611_ = lean_string_append(v___x_2610_, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2613_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__12, &l_Lean_instFromJsonSerialMessage_fromJson___closed__12_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__12);
v___x_2614_ = lean_string_append(v___x_2613_, v___x_2612_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2615_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__31);
v___x_2616_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2617_ = lean_string_append(v___x_2616_, v___x_2615_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2618_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2619_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__14, &l_Lean_instFromJsonSerialMessage_fromJson___closed__14_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__14);
v___x_2620_ = lean_string_append(v___x_2619_, v___x_2618_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__35);
v___x_2622_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2623_ = lean_string_append(v___x_2622_, v___x_2621_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2624_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2625_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__16, &l_Lean_instFromJsonSerialMessage_fromJson___closed__16_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__16);
v___x_2626_ = lean_string_append(v___x_2625_, v___x_2624_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39, &l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39_once, _init_l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__39);
v___x_2628_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2629_ = lean_string_append(v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2631_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__18, &l_Lean_instFromJsonSerialMessage_fromJson___closed__18_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__18);
v___x_2632_ = lean_string_append(v___x_2631_, v___x_2630_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21(void){
_start:
{
uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = 1;
v___x_2636_ = ((lean_object*)(l_Lean_instFromJsonSerialMessage_fromJson___closed__20));
v___x_2637_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__21, &l_Lean_instFromJsonSerialMessage_fromJson___closed__21_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__21);
v___x_2639_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__3, &l_Lean_instFromJsonSerialMessage_fromJson___closed__3_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__3);
v___x_2640_ = lean_string_append(v___x_2639_, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lean_instFromJsonBaseMessage_fromJson___redArg___closed__9));
v___x_2642_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__22, &l_Lean_instFromJsonSerialMessage_fromJson___closed__22_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__22);
v___x_2643_ = lean_string_append(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object* v_json_2644_){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
lean_inc(v_json_2644_);
v___x_2646_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2644_, v___x_2645_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2656_; 
lean_dec(v_json_2644_);
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
v___x_2651_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__5, &l_Lean_instFromJsonSerialMessage_fromJson___closed__5_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__5);
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
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_json_2644_);
v_a_2657_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2646_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2646_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set_tag(v___x_2659_, 0);
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
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
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_a_2665_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2666_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
lean_inc(v_json_2644_);
v___x_2667_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__1(v_json_2644_, v___x_2666_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__7, &l_Lean_instFromJsonSerialMessage_fromJson___closed__7_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__7);
v___x_2673_ = lean_string_append(v___x_2672_, v_a_2668_);
lean_dec(v_a_2668_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2673_);
v___x_2675_ = v___x_2670_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2678_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2667_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2667_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 0);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
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
lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_a_2686_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2687_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
lean_inc(v_json_2644_);
v___x_2688_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__2(v_json_2644_, v___x_2687_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2698_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2693_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__9, &l_Lean_instFromJsonSerialMessage_fromJson___closed__9_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__9);
v___x_2694_ = lean_string_append(v___x_2693_, v_a_2689_);
lean_dec(v_a_2689_);
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___x_2694_);
v___x_2696_ = v___x_2691_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
else
{
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2699_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2688_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2688_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set_tag(v___x_2701_, 0);
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
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
lean_object* v_a_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_a_2707_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2708_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
lean_inc(v_json_2644_);
v___x_2709_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2644_, v___x_2708_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__11, &l_Lean_instFromJsonSerialMessage_fromJson___closed__11_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__11);
v___x_2715_ = lean_string_append(v___x_2714_, v_a_2710_);
lean_dec(v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2717_ = v___x_2712_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
else
{
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2720_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2709_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2709_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 0);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
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
lean_object* v_a_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_a_2728_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2729_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
lean_inc(v_json_2644_);
v___x_2730_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__4(v_json_2644_, v___x_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2740_; 
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__13, &l_Lean_instFromJsonSerialMessage_fromJson___closed__13_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__13);
v___x_2736_ = lean_string_append(v___x_2735_, v_a_2731_);
lean_dec(v_a_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2736_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2741_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2730_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2730_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 0);
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
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
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_a_2749_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2750_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
lean_inc(v_json_2644_);
v___x_2751_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__3(v_json_2644_, v___x_2750_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2761_; 
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2761_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__15, &l_Lean_instFromJsonSerialMessage_fromJson___closed__15_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__15);
v___x_2757_ = lean_string_append(v___x_2756_, v_a_2752_);
lean_dec(v_a_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2757_);
v___x_2759_ = v___x_2754_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
else
{
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2762_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2751_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2751_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 0);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
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
lean_object* v_a_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2770_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2771_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
lean_inc(v_json_2644_);
v___x_2772_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2644_, v___x_2771_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2782_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2777_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__17, &l_Lean_instFromJsonSerialMessage_fromJson___closed__17_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__17);
v___x_2778_ = lean_string_append(v___x_2777_, v_a_2773_);
lean_dec(v_a_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2778_);
v___x_2780_ = v___x_2775_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
else
{
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2783_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2772_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2772_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set_tag(v___x_2785_, 0);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
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
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2791_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2792_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
lean_inc(v_json_2644_);
v___x_2793_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__0(v_json_2644_, v___x_2792_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2791_);
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2798_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__19, &l_Lean_instFromJsonSerialMessage_fromJson___closed__19_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__19);
v___x_2799_ = lean_string_append(v___x_2798_, v_a_2794_);
lean_dec(v_a_2794_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2799_);
v___x_2801_ = v___x_2796_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2791_);
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
lean_dec(v_json_2644_);
v_a_2804_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2793_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2793_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set_tag(v___x_2806_, 0);
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
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
lean_object* v_a_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2812_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2813_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_2814_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_instFromJsonSerialMessage_fromJson_spec__5(v_json_2644_, v___x_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2791_);
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2824_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2824_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
v___x_2819_ = lean_obj_once(&l_Lean_instFromJsonSerialMessage_fromJson___closed__23, &l_Lean_instFromJsonSerialMessage_fromJson___closed__23_once, _init_l_Lean_instFromJsonSerialMessage_fromJson___closed__23);
v___x_2820_ = lean_string_append(v___x_2819_, v_a_2815_);
lean_dec(v_a_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
else
{
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2812_);
lean_dec(v_a_2791_);
lean_dec(v_a_2770_);
lean_dec(v_a_2749_);
lean_dec(v_a_2728_);
lean_dec(v_a_2707_);
lean_dec(v_a_2686_);
lean_dec(v_a_2665_);
v_a_2825_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2814_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2814_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 0);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
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
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2845_; 
v_a_2833_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2835_ = v___x_2814_;
v_isShared_2836_ = v_isSharedCheck_2845_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2814_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2845_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; uint8_t v___x_2838_; uint8_t v___x_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2837_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2837_, 0, v_a_2665_);
lean_ctor_set(v___x_2837_, 1, v_a_2686_);
lean_ctor_set(v___x_2837_, 2, v_a_2707_);
lean_ctor_set(v___x_2837_, 3, v_a_2791_);
lean_ctor_set(v___x_2837_, 4, v_a_2812_);
v___x_2838_ = lean_unbox(v_a_2728_);
lean_dec(v_a_2728_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*5, v___x_2838_);
v___x_2839_ = lean_unbox(v_a_2749_);
lean_dec(v_a_2749_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*5 + 1, v___x_2839_);
v___x_2840_ = lean_unbox(v_a_2770_);
lean_dec(v_a_2770_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*5 + 2, v___x_2840_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2837_);
lean_ctor_set(v___x_2841_, 1, v_a_2833_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2841_);
v___x_2843_ = v___x_2835_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
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
LEAN_EXPORT lean_object* l_Lean_kindOfErrorName(lean_object* v_errorName_2850_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2852_ = l_Lean_Name_str___override(v_errorName_2850_, v___x_2851_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_tagWithErrorName(lean_object* v_msg_2853_, lean_object* v_name_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = l_Lean_kindOfErrorName(v_name_2854_);
v___x_2856_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v_msg_2853_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(lean_object* v_a_2858_){
_start:
{
switch(lean_obj_tag(v_a_2858_))
{
case 0:
{
return v_a_2858_;
}
case 1:
{
lean_object* v_pre_2859_; lean_object* v_str_2860_; lean_object* v_p_x27_2861_; uint8_t v___y_2863_; uint8_t v___x_2866_; 
v_pre_2859_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_pre_2859_);
v_str_2860_ = lean_ctor_get(v_a_2858_, 1);
lean_inc_ref(v_str_2860_);
lean_dec_ref_known(v_a_2858_, 2);
v_p_x27_2861_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2859_);
v___x_2866_ = l_Lean_Name_isAnonymous(v_p_x27_2861_);
if (v___x_2866_ == 0)
{
v___y_2863_ = v___x_2866_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = ((lean_object*)(l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix___closed__0));
v___x_2868_ = lean_string_dec_eq(v_str_2860_, v___x_2867_);
v___y_2863_ = v___x_2868_;
goto v___jp_2862_;
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Name_str___override(v_p_x27_2861_, v_str_2860_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; 
lean_dec(v_p_x27_2861_);
lean_dec_ref(v_str_2860_);
v___x_2865_ = lean_box(0);
return v___x_2865_;
}
}
}
default: 
{
lean_object* v_pre_2869_; lean_object* v_i_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v_pre_2869_ = lean_ctor_get(v_a_2858_, 0);
lean_inc(v_pre_2869_);
v_i_2870_ = lean_ctor_get(v_a_2858_, 1);
lean_inc(v_i_2870_);
lean_dec_ref_known(v_a_2858_, 2);
v___x_2871_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_pre_2869_);
v___x_2872_ = l_Lean_Name_num___override(v___x_2871_, v_i_2870_);
return v___x_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_stripNestedTags(lean_object* v_x_2873_){
_start:
{
switch(lean_obj_tag(v_x_2873_))
{
case 3:
{
lean_object* v_a_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_a_2874_ = lean_ctor_get(v_x_2873_, 0);
v_a_2875_ = lean_ctor_get(v_x_2873_, 1);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2877_ = v_x_2873_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_inc(v_a_2874_);
lean_dec(v_x_2873_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l_Lean_MessageData_stripNestedTags(v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2874_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
case 4:
{
lean_object* v_a_2884_; lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2893_; 
v_a_2884_ = lean_ctor_get(v_x_2873_, 0);
v_a_2885_ = lean_ctor_get(v_x_2873_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2887_ = v_x_2873_;
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_inc(v_a_2884_);
lean_dec(v_x_2873_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2893_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_MessageData_stripNestedTags(v_a_2885_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2884_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
case 8:
{
lean_object* v_a_2894_; lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
v_a_2894_ = lean_ctor_get(v_x_2873_, 0);
v_a_2895_ = lean_ctor_get(v_x_2873_, 1);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2897_ = v_x_2873_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_inc(v_a_2894_);
lean_dec(v_x_2873_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = l___private_Lean_Message_0__Lean_MessageData_stripNestedTags_stripNestedNamePrefix(v_a_2894_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_a_2895_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
case 11:
{
lean_object* v_a_2904_; lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2913_; 
v_a_2904_ = lean_ctor_get(v_x_2873_, 0);
v_a_2905_ = lean_ctor_get(v_x_2873_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_x_2873_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2907_ = v_x_2873_;
v_isShared_2908_ = v_isSharedCheck_2913_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_inc(v_a_2904_);
lean_dec(v_x_2873_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2913_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2909_ = l_Lean_MessageData_stripNestedTags(v_a_2905_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2909_);
v___x_2911_ = v___x_2907_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2904_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
default: 
{
return v_x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f(lean_object* v_x_2914_){
_start:
{
if (lean_obj_tag(v_x_2914_) == 1)
{
lean_object* v_pre_2915_; lean_object* v_str_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; 
v_pre_2915_ = lean_ctor_get(v_x_2914_, 0);
v_str_2916_ = lean_ctor_get(v_x_2914_, 1);
v___x_2917_ = ((lean_object*)(l_Lean_errorNameSuffix___closed__0));
v___x_2918_ = lean_string_dec_eq(v_str_2916_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2919_; 
v___x_2919_ = lean_box(0);
return v___x_2919_;
}
else
{
lean_object* v___x_2920_; 
lean_inc(v_pre_2915_);
v___x_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_pre_2915_);
return v___x_2920_;
}
}
else
{
lean_object* v___x_2921_; 
v___x_2921_ = lean_box(0);
return v___x_2921_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_errorNameOfKind_x3f___boxed(lean_object* v_x_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_errorNameOfKind_x3f(v_x_2922_);
lean_dec(v_x_2922_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f(lean_object* v_msg_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = l_Lean_MessageData_kind(v_msg_2924_);
v___x_2926_ = l_Lean_errorNameOfKind_x3f(v___x_2925_);
lean_dec(v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_errorName_x3f___boxed(lean_object* v_msg_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_MessageData_errorName_x3f(v_msg_2927_);
lean_dec_ref(v_msg_2927_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f(lean_object* v_msg_2929_){
_start:
{
lean_object* v_data_2930_; lean_object* v___x_2931_; 
v_data_2930_ = lean_ctor_get(v_msg_2929_, 4);
v___x_2931_ = l_Lean_MessageData_errorName_x3f(v_data_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_errorName_x3f___boxed(lean_object* v_msg_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Message_errorName_x3f(v_msg_2932_);
lean_dec_ref(v_msg_2932_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toMessage(lean_object* v_msg_2934_){
_start:
{
lean_object* v_toBaseMessage_2935_; lean_object* v_fileName_2936_; lean_object* v_pos_2937_; lean_object* v_endPos_2938_; uint8_t v_keepFullRange_2939_; uint8_t v_severity_2940_; uint8_t v_isSilent_2941_; lean_object* v_caption_2942_; lean_object* v_data_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2952_; 
v_toBaseMessage_2935_ = lean_ctor_get(v_msg_2934_, 0);
lean_inc_ref(v_toBaseMessage_2935_);
lean_dec_ref(v_msg_2934_);
v_fileName_2936_ = lean_ctor_get(v_toBaseMessage_2935_, 0);
v_pos_2937_ = lean_ctor_get(v_toBaseMessage_2935_, 1);
v_endPos_2938_ = lean_ctor_get(v_toBaseMessage_2935_, 2);
v_keepFullRange_2939_ = lean_ctor_get_uint8(v_toBaseMessage_2935_, sizeof(void*)*5);
v_severity_2940_ = lean_ctor_get_uint8(v_toBaseMessage_2935_, sizeof(void*)*5 + 1);
v_isSilent_2941_ = lean_ctor_get_uint8(v_toBaseMessage_2935_, sizeof(void*)*5 + 2);
v_caption_2942_ = lean_ctor_get(v_toBaseMessage_2935_, 3);
v_data_2943_ = lean_ctor_get(v_toBaseMessage_2935_, 4);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_toBaseMessage_2935_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2945_ = v_toBaseMessage_2935_;
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_data_2943_);
lean_inc(v_caption_2942_);
lean_inc(v_endPos_2938_);
lean_inc(v_pos_2937_);
lean_inc(v_fileName_2936_);
lean_dec(v_toBaseMessage_2935_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_data_2943_);
v___x_2948_ = l_Lean_MessageData_ofFormat(v___x_2947_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 4, v___x_2948_);
v___x_2950_ = v___x_2945_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fileName_2936_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_pos_2937_);
lean_ctor_set(v_reuseFailAlloc_2951_, 2, v_endPos_2938_);
lean_ctor_set(v_reuseFailAlloc_2951_, 3, v_caption_2942_);
lean_ctor_set(v_reuseFailAlloc_2951_, 4, v___x_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2951_, sizeof(void*)*5, v_keepFullRange_2939_);
lean_ctor_set_uint8(v_reuseFailAlloc_2951_, sizeof(void*)*5 + 1, v_severity_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_2951_, sizeof(void*)*5 + 2, v_isSilent_2941_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString(lean_object* v_msg_2958_, uint8_t v_includeEndPos_2959_){
_start:
{
lean_object* v___y_2961_; lean_object* v___y_2965_; uint32_t v___y_2966_; lean_object* v___y_2970_; lean_object* v_str_2973_; lean_object* v_toBaseMessage_2983_; lean_object* v_kind_2984_; lean_object* v_fileName_2985_; lean_object* v_pos_2986_; lean_object* v_endPos_2987_; uint8_t v_severity_2988_; lean_object* v_caption_2989_; lean_object* v_data_2990_; lean_object* v___y_2992_; lean_object* v_str_2993_; lean_object* v___y_3001_; 
v_toBaseMessage_2983_ = lean_ctor_get(v_msg_2958_, 0);
lean_inc_ref(v_toBaseMessage_2983_);
v_kind_2984_ = lean_ctor_get(v_msg_2958_, 1);
lean_inc(v_kind_2984_);
lean_dec_ref(v_msg_2958_);
v_fileName_2985_ = lean_ctor_get(v_toBaseMessage_2983_, 0);
lean_inc_ref(v_fileName_2985_);
v_pos_2986_ = lean_ctor_get(v_toBaseMessage_2983_, 1);
lean_inc_ref(v_pos_2986_);
v_endPos_2987_ = lean_ctor_get(v_toBaseMessage_2983_, 2);
lean_inc(v_endPos_2987_);
v_severity_2988_ = lean_ctor_get_uint8(v_toBaseMessage_2983_, sizeof(void*)*5 + 1);
v_caption_2989_ = lean_ctor_get(v_toBaseMessage_2983_, 3);
lean_inc_ref(v_caption_2989_);
v_data_2990_ = lean_ctor_get(v_toBaseMessage_2983_, 4);
lean_inc(v_data_2990_);
lean_dec_ref(v_toBaseMessage_2983_);
if (v_includeEndPos_2959_ == 0)
{
lean_object* v___x_3007_; 
lean_dec(v_endPos_2987_);
v___x_3007_ = lean_box(0);
v___y_3001_ = v___x_3007_;
goto v___jp_3000_;
}
else
{
v___y_3001_ = v_endPos_2987_;
goto v___jp_3000_;
}
v___jp_2960_:
{
lean_object* v___x_2962_; lean_object* v_str_2963_; 
v___x_2962_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_2963_ = lean_string_append(v___y_2961_, v___x_2962_);
return v_str_2963_;
}
v___jp_2964_:
{
uint32_t v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = 10;
v___x_2968_ = lean_uint32_dec_eq(v___y_2966_, v___x_2967_);
if (v___x_2968_ == 0)
{
v___y_2961_ = v___y_2965_;
goto v___jp_2960_;
}
else
{
return v___y_2965_;
}
}
v___jp_2969_:
{
uint32_t v___x_2971_; 
v___x_2971_ = 65;
v___y_2965_ = v___y_2970_;
v___y_2966_ = v___x_2971_;
goto v___jp_2964_;
}
v___jp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2974_ = lean_string_utf8_byte_size(v_str_2973_);
v___x_2975_ = lean_unsigned_to_nat(0u);
v___x_2976_ = lean_nat_dec_eq(v___x_2974_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_inc_ref(v_str_2973_);
v___x_2977_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2977_, 0, v_str_2973_);
lean_ctor_set(v___x_2977_, 1, v___x_2975_);
lean_ctor_set(v___x_2977_, 2, v___x_2974_);
v___x_2978_ = l_String_Slice_Pos_prev_x3f(v___x_2977_, v___x_2974_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_dec_ref_known(v___x_2977_, 3);
v___y_2970_ = v_str_2973_;
goto v___jp_2969_;
}
else
{
lean_object* v_val_2979_; lean_object* v___x_2980_; 
v_val_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_val_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l_String_Slice_Pos_get_x3f(v___x_2977_, v_val_2979_);
lean_dec(v_val_2979_);
lean_dec_ref_known(v___x_2977_, 3);
if (lean_obj_tag(v___x_2980_) == 0)
{
v___y_2970_ = v_str_2973_;
goto v___jp_2969_;
}
else
{
lean_object* v_val_2981_; uint32_t v___x_2982_; 
v_val_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_val_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = lean_unbox_uint32(v_val_2981_);
lean_dec(v_val_2981_);
v___y_2965_ = v_str_2973_;
v___y_2966_ = v___x_2982_;
goto v___jp_2964_;
}
}
}
else
{
v___y_2961_ = v_str_2973_;
goto v___jp_2960_;
}
}
v___jp_2991_:
{
switch(v_severity_2988_)
{
case 0:
{
lean_dec(v___y_2992_);
lean_dec_ref(v_pos_2986_);
lean_dec_ref(v_fileName_2985_);
lean_dec(v_kind_2984_);
v_str_2973_ = v_str_2993_;
goto v___jp_2972_;
}
case 1:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_str_2996_; 
v___x_2994_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_2995_ = l_Lean_errorNameOfKind_x3f(v_kind_2984_);
lean_dec(v_kind_2984_);
v_str_2996_ = l_Lean_mkErrorStringWithPos(v_fileName_2985_, v_pos_2986_, v_str_2993_, v___y_2992_, v___x_2994_, v___x_2995_);
lean_dec_ref(v_str_2993_);
v_str_2973_ = v_str_2996_;
goto v___jp_2972_;
}
default: 
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v_str_2999_; 
v___x_2997_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_2998_ = l_Lean_errorNameOfKind_x3f(v_kind_2984_);
lean_dec(v_kind_2984_);
v_str_2999_ = l_Lean_mkErrorStringWithPos(v_fileName_2985_, v_pos_2986_, v_str_2993_, v___y_2992_, v___x_2997_, v___x_2998_);
lean_dec_ref(v_str_2993_);
v_str_2973_ = v_str_2999_;
goto v___jp_2972_;
}
}
}
v___jp_3000_:
{
lean_object* v___x_3002_; uint8_t v___x_3003_; 
v___x_3002_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3003_ = lean_string_dec_eq(v_caption_2989_, v___x_3002_);
if (v___x_3003_ == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v_str_3006_; 
v___x_3004_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3005_ = lean_string_append(v_caption_2989_, v___x_3004_);
v_str_3006_ = lean_string_append(v___x_3005_, v_data_2990_);
lean_dec(v_data_2990_);
v___y_2992_ = v___y_3001_;
v_str_2993_ = v_str_3006_;
goto v___jp_2991_;
}
else
{
lean_dec_ref(v_caption_2989_);
v___y_2992_ = v___y_3001_;
v_str_2993_ = v_data_2990_;
goto v___jp_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_toString___boxed(lean_object* v_msg_3008_, lean_object* v_includeEndPos_3009_){
_start:
{
uint8_t v_includeEndPos_boxed_3010_; lean_object* v_res_3011_; 
v_includeEndPos_boxed_3010_ = lean_unbox(v_includeEndPos_3009_);
v_res_3011_ = l_Lean_SerialMessage_toString(v_msg_3008_, v_includeEndPos_boxed_3010_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_SerialMessage_instToString___lam__0(lean_object* v_msg_3012_){
_start:
{
uint8_t v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = 0;
v___x_3014_ = l_Lean_SerialMessage_toString(v_msg_3012_, v___x_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind(lean_object* v_msg_3017_){
_start:
{
lean_object* v_data_3018_; lean_object* v___x_3019_; 
v_data_3018_ = lean_ctor_get(v_msg_3017_, 4);
v___x_3019_ = l_Lean_MessageData_kind(v_data_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_kind___boxed(lean_object* v_msg_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Message_kind(v_msg_3020_);
lean_dec_ref(v_msg_3020_);
return v_res_3021_;
}
}
LEAN_EXPORT uint8_t l_Lean_Message_isTrace(lean_object* v_msg_3022_){
_start:
{
lean_object* v_data_3023_; uint8_t v___x_3024_; 
v_data_3023_ = lean_ctor_get(v_msg_3022_, 4);
v___x_3024_ = l_Lean_MessageData_isTrace(v_data_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_isTrace___boxed(lean_object* v_msg_3025_){
_start:
{
uint8_t v_res_3026_; lean_object* v_r_3027_; 
v_res_3026_ = l_Lean_Message_isTrace(v_msg_3025_);
lean_dec_ref(v_msg_3025_);
v_r_3027_ = lean_box(v_res_3026_);
return v_r_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize(lean_object* v_msg_3028_){
_start:
{
lean_object* v_fileName_3030_; lean_object* v_pos_3031_; lean_object* v_endPos_3032_; uint8_t v_keepFullRange_3033_; uint8_t v_severity_3034_; uint8_t v_isSilent_3035_; lean_object* v_caption_3036_; lean_object* v_data_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3047_; 
v_fileName_3030_ = lean_ctor_get(v_msg_3028_, 0);
v_pos_3031_ = lean_ctor_get(v_msg_3028_, 1);
v_endPos_3032_ = lean_ctor_get(v_msg_3028_, 2);
v_keepFullRange_3033_ = lean_ctor_get_uint8(v_msg_3028_, sizeof(void*)*5);
v_severity_3034_ = lean_ctor_get_uint8(v_msg_3028_, sizeof(void*)*5 + 1);
v_isSilent_3035_ = lean_ctor_get_uint8(v_msg_3028_, sizeof(void*)*5 + 2);
v_caption_3036_ = lean_ctor_get(v_msg_3028_, 3);
v_data_3037_ = lean_ctor_get(v_msg_3028_, 4);
v_isSharedCheck_3047_ = !lean_is_exclusive(v_msg_3028_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3039_ = v_msg_3028_;
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_data_3037_);
lean_inc(v_caption_3036_);
lean_inc(v_endPos_3032_);
lean_inc(v_pos_3031_);
lean_inc(v_fileName_3030_);
lean_dec(v_msg_3028_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3047_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_inc(v_data_3037_);
v___x_3041_ = l_Lean_MessageData_toString(v_data_3037_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 4, v___x_3041_);
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_fileName_3030_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v_pos_3031_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v_endPos_3032_);
lean_ctor_set(v_reuseFailAlloc_3046_, 3, v_caption_3036_);
lean_ctor_set(v_reuseFailAlloc_3046_, 4, v___x_3041_);
lean_ctor_set_uint8(v_reuseFailAlloc_3046_, sizeof(void*)*5, v_keepFullRange_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3046_, sizeof(void*)*5 + 1, v_severity_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3046_, sizeof(void*)*5 + 2, v_isSilent_3035_);
v___x_3043_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3044_ = l_Lean_MessageData_kind(v_data_3037_);
lean_dec(v_data_3037_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
return v___x_3045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_serialize___boxed(lean_object* v_msg_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_Message_serialize(v_msg_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString(lean_object* v_msg_3051_, uint8_t v_includeEndPos_3052_){
_start:
{
lean_object* v_fileName_3054_; lean_object* v_pos_3055_; lean_object* v_endPos_3056_; uint8_t v_severity_3057_; lean_object* v_caption_3058_; lean_object* v_data_3059_; lean_object* v___x_3060_; lean_object* v___y_3062_; lean_object* v___y_3066_; uint32_t v___y_3067_; lean_object* v___y_3071_; lean_object* v_str_3074_; lean_object* v___x_3084_; lean_object* v___y_3086_; lean_object* v_str_3087_; lean_object* v___y_3095_; 
v_fileName_3054_ = lean_ctor_get(v_msg_3051_, 0);
lean_inc_ref(v_fileName_3054_);
v_pos_3055_ = lean_ctor_get(v_msg_3051_, 1);
lean_inc_ref(v_pos_3055_);
v_endPos_3056_ = lean_ctor_get(v_msg_3051_, 2);
lean_inc(v_endPos_3056_);
v_severity_3057_ = lean_ctor_get_uint8(v_msg_3051_, sizeof(void*)*5 + 1);
v_caption_3058_ = lean_ctor_get(v_msg_3051_, 3);
lean_inc_ref(v_caption_3058_);
v_data_3059_ = lean_ctor_get(v_msg_3051_, 4);
lean_inc_n(v_data_3059_, 2);
lean_dec_ref(v_msg_3051_);
v___x_3060_ = l_Lean_MessageData_toString(v_data_3059_);
v___x_3084_ = l_Lean_MessageData_kind(v_data_3059_);
lean_dec(v_data_3059_);
if (v_includeEndPos_3052_ == 0)
{
lean_object* v___x_3101_; 
lean_dec(v_endPos_3056_);
v___x_3101_ = lean_box(0);
v___y_3095_ = v___x_3101_;
goto v___jp_3094_;
}
else
{
v___y_3095_ = v_endPos_3056_;
goto v___jp_3094_;
}
v___jp_3061_:
{
lean_object* v___x_3063_; lean_object* v_str_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__1));
v_str_3064_ = lean_string_append(v___y_3062_, v___x_3063_);
return v_str_3064_;
}
v___jp_3065_:
{
uint32_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3068_ = 10;
v___x_3069_ = lean_uint32_dec_eq(v___y_3067_, v___x_3068_);
if (v___x_3069_ == 0)
{
v___y_3062_ = v___y_3066_;
goto v___jp_3061_;
}
else
{
return v___y_3066_;
}
}
v___jp_3070_:
{
uint32_t v___x_3072_; 
v___x_3072_ = 65;
v___y_3066_ = v___y_3071_;
v___y_3067_ = v___x_3072_;
goto v___jp_3065_;
}
v___jp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v___x_3075_ = lean_string_utf8_byte_size(v_str_3074_);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = lean_nat_dec_eq(v___x_3075_, v___x_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_ref(v_str_3074_);
v___x_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3078_, 0, v_str_3074_);
lean_ctor_set(v___x_3078_, 1, v___x_3076_);
lean_ctor_set(v___x_3078_, 2, v___x_3075_);
v___x_3079_ = l_String_Slice_Pos_prev_x3f(v___x_3078_, v___x_3075_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_dec_ref_known(v___x_3078_, 3);
v___y_3071_ = v_str_3074_;
goto v___jp_3070_;
}
else
{
lean_object* v_val_3080_; lean_object* v___x_3081_; 
v_val_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l_String_Slice_Pos_get_x3f(v___x_3078_, v_val_3080_);
lean_dec(v_val_3080_);
lean_dec_ref_known(v___x_3078_, 3);
if (lean_obj_tag(v___x_3081_) == 0)
{
v___y_3071_ = v_str_3074_;
goto v___jp_3070_;
}
else
{
lean_object* v_val_3082_; uint32_t v___x_3083_; 
v_val_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v___x_3083_ = lean_unbox_uint32(v_val_3082_);
lean_dec(v_val_3082_);
v___y_3066_ = v_str_3074_;
v___y_3067_ = v___x_3083_;
goto v___jp_3065_;
}
}
}
else
{
v___y_3062_ = v_str_3074_;
goto v___jp_3061_;
}
}
v___jp_3085_:
{
switch(v_severity_3057_)
{
case 0:
{
lean_dec(v___y_3086_);
lean_dec(v___x_3084_);
lean_dec_ref(v_pos_3055_);
lean_dec_ref(v_fileName_3054_);
v_str_3074_ = v_str_3087_;
goto v___jp_3073_;
}
case 1:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_str_3090_; 
v___x_3088_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__0));
v___x_3089_ = l_Lean_errorNameOfKind_x3f(v___x_3084_);
lean_dec(v___x_3084_);
v_str_3090_ = l_Lean_mkErrorStringWithPos(v_fileName_3054_, v_pos_3055_, v_str_3087_, v___y_3086_, v___x_3088_, v___x_3089_);
lean_dec_ref(v_str_3087_);
v_str_3074_ = v_str_3090_;
goto v___jp_3073_;
}
default: 
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v_str_3093_; 
v___x_3091_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__1));
v___x_3092_ = l_Lean_errorNameOfKind_x3f(v___x_3084_);
lean_dec(v___x_3084_);
v_str_3093_ = l_Lean_mkErrorStringWithPos(v_fileName_3054_, v_pos_3055_, v_str_3087_, v___y_3086_, v___x_3091_, v___x_3092_);
lean_dec_ref(v_str_3087_);
v_str_3074_ = v_str_3093_;
goto v___jp_3073_;
}
}
}
v___jp_3094_:
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_3097_ = lean_string_dec_eq(v_caption_3058_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_str_3100_; 
v___x_3098_ = ((lean_object*)(l_Lean_SerialMessage_toString___closed__2));
v___x_3099_ = lean_string_append(v_caption_3058_, v___x_3098_);
v_str_3100_ = lean_string_append(v___x_3099_, v___x_3060_);
lean_dec_ref(v___x_3060_);
v___y_3086_ = v___y_3095_;
v_str_3087_ = v_str_3100_;
goto v___jp_3085_;
}
else
{
lean_dec_ref(v_caption_3058_);
v___y_3086_ = v___y_3095_;
v_str_3087_ = v___x_3060_;
goto v___jp_3085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toString___boxed(lean_object* v_msg_3102_, lean_object* v_includeEndPos_3103_, lean_object* v_a_3104_){
_start:
{
uint8_t v_includeEndPos_boxed_3105_; lean_object* v_res_3106_; 
v_includeEndPos_boxed_3105_ = lean_unbox(v_includeEndPos_3103_);
v_res_3106_ = l_Lean_Message_toString(v_msg_3102_, v_includeEndPos_boxed_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson(lean_object* v_msg_3107_){
_start:
{
lean_object* v_fileName_3109_; lean_object* v_pos_3110_; lean_object* v_endPos_3111_; uint8_t v_keepFullRange_3112_; uint8_t v_severity_3113_; uint8_t v_isSilent_3114_; lean_object* v_caption_3115_; lean_object* v_data_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_fileName_3109_ = lean_ctor_get(v_msg_3107_, 0);
lean_inc_ref(v_fileName_3109_);
v_pos_3110_ = lean_ctor_get(v_msg_3107_, 1);
lean_inc_ref(v_pos_3110_);
v_endPos_3111_ = lean_ctor_get(v_msg_3107_, 2);
lean_inc(v_endPos_3111_);
v_keepFullRange_3112_ = lean_ctor_get_uint8(v_msg_3107_, sizeof(void*)*5);
v_severity_3113_ = lean_ctor_get_uint8(v_msg_3107_, sizeof(void*)*5 + 1);
v_isSilent_3114_ = lean_ctor_get_uint8(v_msg_3107_, sizeof(void*)*5 + 2);
v_caption_3115_ = lean_ctor_get(v_msg_3107_, 3);
lean_inc_ref(v_caption_3115_);
v_data_3116_ = lean_ctor_get(v_msg_3107_, 4);
lean_inc_n(v_data_3116_, 2);
lean_dec_ref(v_msg_3107_);
v___x_3117_ = l_Lean_MessageData_toString(v_data_3116_);
v___x_3118_ = l_Lean_MessageData_kind(v_data_3116_);
lean_dec(v_data_3116_);
v___x_3119_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__1));
v___x_3120_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3120_, 0, v_fileName_3109_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_box(0);
v___x_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__2));
v___x_3125_ = l_Lean_instToJsonPosition_toJson(v_pos_3110_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3122_);
v___x_3128_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__3));
v___x_3129_ = l_Lean_Option_toJson___at___00Lean_instToJsonSerialMessage_toJson_spec__0(v_endPos_3111_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
lean_ctor_set(v___x_3131_, 1, v___x_3122_);
v___x_3132_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__4));
v___x_3133_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3133_, 0, v_keepFullRange_3112_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3134_);
lean_ctor_set(v___x_3135_, 1, v___x_3122_);
v___x_3136_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__5));
v___x_3137_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_3113_);
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v___x_3122_);
v___x_3140_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__6));
v___x_3141_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3141_, 0, v_isSilent_3114_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v___x_3122_);
v___x_3144_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__7));
v___x_3145_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3145_, 0, v_caption_3115_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3144_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3122_);
v___x_3148_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__8));
v___x_3149_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3117_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3148_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___x_3122_);
v___x_3152_ = ((lean_object*)(l_Lean_instToJsonSerialMessage_toJson___closed__0));
v___x_3153_ = 1;
v___x_3154_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3118_, v___x_3153_);
v___x_3155_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3152_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v___x_3122_);
v___x_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v___x_3122_);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3151_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3147_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3143_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3139_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3135_);
lean_ctor_set(v___x_3163_, 1, v___x_3162_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3131_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3127_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3123_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = ((lean_object*)(l_Lean_instToJsonBaseMessage_toJson___redArg___closed__10));
v___x_3168_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_instToJsonSerialMessage_toJson_spec__1(v___x_3166_, v___x_3167_);
v___x_3169_ = l_Lean_Json_mkObj(v___x_3168_);
lean_dec(v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Message_toJson___boxed(lean_object* v_msg_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_Message_toJson(v_msg_3170_);
return v_res_3172_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__0(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = lean_unsigned_to_nat(32u);
v___x_3174_ = lean_mk_empty_array_with_capacity(v___x_3173_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__1(void){
_start:
{
size_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3176_ = ((size_t)5ULL);
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = lean_unsigned_to_nat(32u);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3180_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__0, &l_Lean_instInhabitedMessageLog_default___closed__0_once, _init_l_Lean_instInhabitedMessageLog_default___closed__0);
v___x_3181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3179_);
lean_ctor_set(v___x_3181_, 2, v___x_3177_);
lean_ctor_set(v___x_3181_, 3, v___x_3177_);
lean_ctor_set_usize(v___x_3181_, 4, v___x_3176_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default___closed__2(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = l_Lean_NameSet_empty;
v___x_3183_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v___x_3184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
lean_ctor_set(v___x_3184_, 2, v___x_3182_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog_default(void){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_instInhabitedMessageLog(void){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Lean_instInhabitedMessageLog_default;
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_MessageLog_empty(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_unsigned_to_nat(32u);
v___x_3188_ = lean_mk_empty_array_with_capacity(v___x_3187_);
lean_dec_ref(v___x_3188_);
v___x_3189_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__2, &l_Lean_instInhabitedMessageLog_default___closed__2_once, _init_l_Lean_instInhabitedMessageLog_default___closed__2);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs(lean_object* v_self_3190_){
_start:
{
lean_object* v_unreported_3191_; 
v_unreported_3191_ = lean_ctor_get(v_self_3190_, 1);
lean_inc_ref(v_unreported_3191_);
return v_unreported_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_msgs___boxed(lean_object* v_self_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_MessageLog_msgs(v_self_3192_);
lean_dec_ref(v_self_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_reportedPlusUnreported(lean_object* v_x_3194_){
_start:
{
lean_object* v_reported_3195_; lean_object* v_unreported_3196_; lean_object* v___x_3197_; 
v_reported_3195_ = lean_ctor_get(v_x_3194_, 0);
lean_inc_ref(v_reported_3195_);
v_unreported_3196_ = lean_ctor_get(v_x_3194_, 1);
lean_inc_ref(v_unreported_3196_);
lean_dec_ref(v_x_3194_);
v___x_3197_ = l_Lean_PersistentArray_append___redArg(v_reported_3195_, v_unreported_3196_);
lean_dec_ref(v_unreported_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasUnreported(lean_object* v_log_3198_){
_start:
{
lean_object* v_unreported_3199_; uint8_t v___x_3200_; 
v_unreported_3199_ = lean_ctor_get(v_log_3198_, 1);
v___x_3200_ = l_Lean_PersistentArray_isEmpty___redArg(v_unreported_3199_);
if (v___x_3200_ == 0)
{
uint8_t v___x_3201_; 
v___x_3201_ = 1;
return v___x_3201_;
}
else
{
uint8_t v___x_3202_; 
v___x_3202_ = 0;
return v___x_3202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasUnreported___boxed(lean_object* v_log_3203_){
_start:
{
uint8_t v_res_3204_; lean_object* v_r_3205_; 
v_res_3204_ = l_Lean_MessageLog_hasUnreported(v_log_3203_);
lean_dec_ref(v_log_3203_);
v_r_3205_ = lean_box(v_res_3204_);
return v_r_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_add(lean_object* v_msg_3206_, lean_object* v_log_3207_){
_start:
{
lean_object* v_reported_3208_; lean_object* v_unreported_3209_; lean_object* v_loggedKinds_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3218_; 
v_reported_3208_ = lean_ctor_get(v_log_3207_, 0);
v_unreported_3209_ = lean_ctor_get(v_log_3207_, 1);
v_loggedKinds_3210_ = lean_ctor_get(v_log_3207_, 2);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_log_3207_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3212_ = v_log_3207_;
v_isShared_3213_ = v_isSharedCheck_3218_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_loggedKinds_3210_);
lean_inc(v_unreported_3209_);
lean_inc(v_reported_3208_);
lean_dec(v_log_3207_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3218_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = l_Lean_PersistentArray_push___redArg(v_unreported_3209_, v_msg_3206_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 1, v___x_3214_);
v___x_3216_ = v___x_3212_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_reported_3208_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3217_, 2, v_loggedKinds_3210_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(lean_object* v_b_u2082_3221_, lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_b_u2082_3221_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; 
v___x_3224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___closed__0));
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0___boxed(lean_object* v_b_u2082_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3225_, v_x_3226_);
lean_dec(v_x_3226_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(lean_object* v_b_u2082_3228_, lean_object* v_k_3229_, lean_object* v_t_3230_){
_start:
{
if (lean_obj_tag(v_t_3230_) == 0)
{
lean_object* v_size_3231_; lean_object* v_k_3232_; lean_object* v_v_3233_; lean_object* v_l_3234_; lean_object* v_r_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3250_; 
v_size_3231_ = lean_ctor_get(v_t_3230_, 0);
v_k_3232_ = lean_ctor_get(v_t_3230_, 1);
v_v_3233_ = lean_ctor_get(v_t_3230_, 2);
v_l_3234_ = lean_ctor_get(v_t_3230_, 3);
v_r_3235_ = lean_ctor_get(v_t_3230_, 4);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_t_3230_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3237_ = v_t_3230_;
v_isShared_3238_ = v_isSharedCheck_3250_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_r_3235_);
lean_inc(v_l_3234_);
lean_inc(v_v_3233_);
lean_inc(v_k_3232_);
lean_inc(v_size_3231_);
lean_dec(v_t_3230_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3250_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
uint8_t v___x_3239_; 
v___x_3239_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3229_, v_k_3232_);
switch(v___x_3239_)
{
case 0:
{
lean_object* v_impl_3240_; lean_object* v___x_3241_; 
lean_del_object(v___x_3237_);
lean_dec(v_size_3231_);
v_impl_3240_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3228_, v_k_3229_, v_l_3234_);
v___x_3241_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3232_, v_v_3233_, v_impl_3240_, v_r_3235_);
return v___x_3241_;
}
case 1:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v_val_3244_; lean_object* v___x_3246_; 
lean_dec(v_k_3232_);
v___x_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3242_, 0, v_v_3233_);
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3228_, v___x_3242_);
lean_dec_ref_known(v___x_3242_, 1);
v_val_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_val_3244_);
lean_dec(v___x_3243_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 2, v_val_3244_);
lean_ctor_set(v___x_3237_, 1, v_k_3229_);
v___x_3246_ = v___x_3237_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_size_3231_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_k_3229_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_val_3244_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_l_3234_);
lean_ctor_set(v_reuseFailAlloc_3247_, 4, v_r_3235_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
default: 
{
lean_object* v_impl_3248_; lean_object* v___x_3249_; 
lean_del_object(v___x_3237_);
lean_dec(v_size_3231_);
v_impl_3248_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3228_, v_k_3229_, v_r_3235_);
v___x_3249_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_3232_, v_v_3233_, v_l_3234_, v_impl_3248_);
return v___x_3249_;
}
}
}
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v_val_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3251_ = lean_box(0);
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg___lam__0(v_b_u2082_3228_, v___x_3251_);
v_val_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_val_3253_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v_k_3229_);
lean_ctor_set(v___x_3255_, 2, v_val_3253_);
lean_ctor_set(v___x_3255_, 3, v_t_3230_);
lean_ctor_set(v___x_3255_, 4, v_t_3230_);
return v___x_3255_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(lean_object* v_init_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_object* v_k_3258_; lean_object* v_v_3259_; lean_object* v_l_3260_; lean_object* v_r_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_k_3258_ = lean_ctor_get(v_x_3257_, 1);
lean_inc(v_k_3258_);
v_v_3259_ = lean_ctor_get(v_x_3257_, 2);
lean_inc(v_v_3259_);
v_l_3260_ = lean_ctor_get(v_x_3257_, 3);
lean_inc(v_l_3260_);
v_r_3261_ = lean_ctor_get(v_x_3257_, 4);
lean_inc(v_r_3261_);
lean_dec_ref_known(v_x_3257_, 5);
v___x_3262_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3256_, v_l_3260_);
v___x_3263_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_v_3259_, v_k_3258_, v___x_3262_);
v_init_3256_ = v___x_3263_;
v_x_3257_ = v_r_3261_;
goto _start;
}
else
{
return v_init_3256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_append(lean_object* v_l_u2081_3265_, lean_object* v_l_u2082_3266_){
_start:
{
lean_object* v_reported_3267_; lean_object* v_unreported_3268_; lean_object* v_loggedKinds_3269_; lean_object* v_reported_3270_; lean_object* v_unreported_3271_; lean_object* v_loggedKinds_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3282_; 
v_reported_3267_ = lean_ctor_get(v_l_u2081_3265_, 0);
lean_inc_ref(v_reported_3267_);
v_unreported_3268_ = lean_ctor_get(v_l_u2081_3265_, 1);
lean_inc_ref(v_unreported_3268_);
v_loggedKinds_3269_ = lean_ctor_get(v_l_u2081_3265_, 2);
lean_inc(v_loggedKinds_3269_);
lean_dec_ref(v_l_u2081_3265_);
v_reported_3270_ = lean_ctor_get(v_l_u2082_3266_, 0);
v_unreported_3271_ = lean_ctor_get(v_l_u2082_3266_, 1);
v_loggedKinds_3272_ = lean_ctor_get(v_l_u2082_3266_, 2);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_l_u2082_3266_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3274_ = v_l_u2082_3266_;
v_isShared_3275_ = v_isSharedCheck_3282_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_loggedKinds_3272_);
lean_inc(v_unreported_3271_);
lean_inc(v_reported_3270_);
lean_dec(v_l_u2082_3266_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3282_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
v___x_3276_ = l_Lean_PersistentArray_append___redArg(v_reported_3267_, v_reported_3270_);
lean_dec_ref(v_reported_3270_);
v___x_3277_ = l_Lean_PersistentArray_append___redArg(v_unreported_3268_, v_unreported_3271_);
lean_dec_ref(v_unreported_3271_);
v___x_3278_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_loggedKinds_3269_, v_loggedKinds_3272_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 2, v___x_3278_);
lean_ctor_set(v___x_3274_, 1, v___x_3277_);
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3280_ = v___x_3274_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___x_3277_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v___x_3278_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0(lean_object* v_b_u2082_3283_, lean_object* v_k_3284_, lean_object* v_t_3285_, lean_object* v_hl_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_MessageLog_append_spec__0___redArg(v_b_u2082_3283_, v_k_3284_, v_t_3285_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1(lean_object* v_init_3288_, lean_object* v_t_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_MessageLog_append_spec__1_spec__1(v_init_3288_, v_t_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(lean_object* v_as_3293_, size_t v_i_3294_, size_t v_stop_3295_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_eq(v_i_3294_, v_stop_3295_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; uint8_t v_severity_3298_; 
v___x_3297_ = lean_array_uget_borrowed(v_as_3293_, v_i_3294_);
v_severity_3298_ = lean_ctor_get_uint8(v___x_3297_, sizeof(void*)*5 + 1);
if (v_severity_3298_ == 2)
{
uint8_t v___x_3299_; 
v___x_3299_ = 1;
return v___x_3299_;
}
else
{
size_t v___x_3300_; size_t v___x_3301_; 
v___x_3300_ = ((size_t)1ULL);
v___x_3301_ = lean_usize_add(v_i_3294_, v___x_3300_);
v_i_3294_ = v___x_3301_;
goto _start;
}
}
else
{
uint8_t v___x_3303_; 
v___x_3303_ = 0;
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1___boxed(lean_object* v_as_3304_, lean_object* v_i_3305_, lean_object* v_stop_3306_){
_start:
{
size_t v_i_boxed_3307_; size_t v_stop_boxed_3308_; uint8_t v_res_3309_; lean_object* v_r_3310_; 
v_i_boxed_3307_ = lean_unbox_usize(v_i_3305_);
lean_dec(v_i_3305_);
v_stop_boxed_3308_ = lean_unbox_usize(v_stop_3306_);
lean_dec(v_stop_3306_);
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_as_3304_, v_i_boxed_3307_, v_stop_boxed_3308_);
lean_dec_ref(v_as_3304_);
v_r_3310_ = lean_box(v_res_3309_);
return v_r_3310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(lean_object* v_x_3311_){
_start:
{
if (lean_obj_tag(v_x_3311_) == 0)
{
lean_object* v_cs_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; uint8_t v___x_3315_; 
v_cs_3312_ = lean_ctor_get(v_x_3311_, 0);
v___x_3313_ = lean_unsigned_to_nat(0u);
v___x_3314_ = lean_array_get_size(v_cs_3312_);
v___x_3315_ = lean_nat_dec_lt(v___x_3313_, v___x_3314_);
if (v___x_3315_ == 0)
{
return v___x_3315_;
}
else
{
if (v___x_3315_ == 0)
{
return v___x_3315_;
}
else
{
size_t v___x_3316_; size_t v___x_3317_; uint8_t v___x_3318_; 
v___x_3316_ = ((size_t)0ULL);
v___x_3317_ = lean_usize_of_nat(v___x_3314_);
v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_cs_3312_, v___x_3316_, v___x_3317_);
return v___x_3318_;
}
}
}
else
{
lean_object* v_vs_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_vs_3319_ = lean_ctor_get(v_x_3311_, 0);
v___x_3320_ = lean_unsigned_to_nat(0u);
v___x_3321_ = lean_array_get_size(v_vs_3319_);
v___x_3322_ = lean_nat_dec_lt(v___x_3320_, v___x_3321_);
if (v___x_3322_ == 0)
{
return v___x_3322_;
}
else
{
if (v___x_3322_ == 0)
{
return v___x_3322_;
}
else
{
size_t v___x_3323_; size_t v___x_3324_; uint8_t v___x_3325_; 
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = lean_usize_of_nat(v___x_3321_);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_vs_3319_, v___x_3323_, v___x_3324_);
return v___x_3325_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(lean_object* v_as_3326_, size_t v_i_3327_, size_t v_stop_3328_){
_start:
{
uint8_t v___x_3329_; 
v___x_3329_ = lean_usize_dec_eq(v_i_3327_, v_stop_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; uint8_t v___x_3331_; 
v___x_3330_ = lean_array_uget_borrowed(v_as_3326_, v_i_3327_);
v___x_3331_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v___x_3330_);
if (v___x_3331_ == 0)
{
size_t v___x_3332_; size_t v___x_3333_; 
v___x_3332_ = ((size_t)1ULL);
v___x_3333_ = lean_usize_add(v_i_3327_, v___x_3332_);
v_i_3327_ = v___x_3333_;
goto _start;
}
else
{
return v___x_3331_;
}
}
else
{
uint8_t v___x_3335_; 
v___x_3335_ = 0;
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3336_, lean_object* v_i_3337_, lean_object* v_stop_3338_){
_start:
{
size_t v_i_boxed_3339_; size_t v_stop_boxed_3340_; uint8_t v_res_3341_; lean_object* v_r_3342_; 
v_i_boxed_3339_ = lean_unbox_usize(v_i_3337_);
lean_dec(v_i_3337_);
v_stop_boxed_3340_ = lean_unbox_usize(v_stop_3338_);
lean_dec(v_stop_3338_);
v_res_3341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0_spec__1(v_as_3336_, v_i_boxed_3339_, v_stop_boxed_3340_);
lean_dec_ref(v_as_3336_);
v_r_3342_ = lean_box(v_res_3341_);
return v_r_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0___boxed(lean_object* v_x_3343_){
_start:
{
uint8_t v_res_3344_; lean_object* v_r_3345_; 
v_res_3344_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_x_3343_);
lean_dec_ref(v_x_3343_);
v_r_3345_ = lean_box(v_res_3344_);
return v_r_3345_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(lean_object* v_t_3346_){
_start:
{
lean_object* v_root_3347_; lean_object* v_tail_3348_; uint8_t v___x_3349_; 
v_root_3347_ = lean_ctor_get(v_t_3346_, 0);
v_tail_3348_ = lean_ctor_get(v_t_3346_, 1);
v___x_3349_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__0(v_root_3347_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3350_ = lean_unsigned_to_nat(0u);
v___x_3351_ = lean_array_get_size(v_tail_3348_);
v___x_3352_ = lean_nat_dec_lt(v___x_3350_, v___x_3351_);
if (v___x_3352_ == 0)
{
return v___x_3352_;
}
else
{
if (v___x_3352_ == 0)
{
return v___x_3352_;
}
else
{
size_t v___x_3353_; size_t v___x_3354_; uint8_t v___x_3355_; 
v___x_3353_ = ((size_t)0ULL);
v___x_3354_ = lean_usize_of_nat(v___x_3351_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0_spec__1(v_tail_3348_, v___x_3353_, v___x_3354_);
return v___x_3355_;
}
}
}
else
{
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0___boxed(lean_object* v_t_3356_){
_start:
{
uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_res_3357_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_t_3356_);
lean_dec_ref(v_t_3356_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(uint8_t v___x_3359_, lean_object* v_as_3360_, size_t v_i_3361_, size_t v_stop_3362_){
_start:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_usize_dec_eq(v_i_3361_, v_stop_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; uint8_t v_severity_3365_; uint8_t v___x_3366_; 
v___x_3364_ = lean_array_uget_borrowed(v_as_3360_, v_i_3361_);
v_severity_3365_ = lean_ctor_get_uint8(v___x_3364_, sizeof(void*)*5 + 1);
v___x_3366_ = 1;
if (v_severity_3365_ == 2)
{
return v___x_3366_;
}
else
{
if (v___x_3359_ == 0)
{
size_t v___x_3367_; size_t v___x_3368_; 
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_add(v_i_3361_, v___x_3367_);
v_i_3361_ = v___x_3368_;
goto _start;
}
else
{
return v___x_3366_;
}
}
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = 0;
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4___boxed(lean_object* v___x_3371_, lean_object* v_as_3372_, lean_object* v_i_3373_, lean_object* v_stop_3374_){
_start:
{
uint8_t v___x_1809__boxed_3375_; size_t v_i_boxed_3376_; size_t v_stop_boxed_3377_; uint8_t v_res_3378_; lean_object* v_r_3379_; 
v___x_1809__boxed_3375_ = lean_unbox(v___x_3371_);
v_i_boxed_3376_ = lean_unbox_usize(v_i_3373_);
lean_dec(v_i_3373_);
v_stop_boxed_3377_ = lean_unbox_usize(v_stop_3374_);
lean_dec(v_stop_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_1809__boxed_3375_, v_as_3372_, v_i_boxed_3376_, v_stop_boxed_3377_);
lean_dec_ref(v_as_3372_);
v_r_3379_ = lean_box(v_res_3378_);
return v_r_3379_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(uint8_t v___x_3380_, lean_object* v_x_3381_){
_start:
{
if (lean_obj_tag(v_x_3381_) == 0)
{
lean_object* v_cs_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v_cs_3382_ = lean_ctor_get(v_x_3381_, 0);
v___x_3383_ = lean_unsigned_to_nat(0u);
v___x_3384_ = lean_array_get_size(v_cs_3382_);
v___x_3385_ = lean_nat_dec_lt(v___x_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
return v___x_3385_;
}
else
{
if (v___x_3385_ == 0)
{
return v___x_3385_;
}
else
{
size_t v___x_3386_; size_t v___x_3387_; uint8_t v___x_3388_; 
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3384_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_3380_, v_cs_3382_, v___x_3386_, v___x_3387_);
return v___x_3388_;
}
}
}
else
{
lean_object* v_vs_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_vs_3389_ = lean_ctor_get(v_x_3381_, 0);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_array_get_size(v_vs_3389_);
v___x_3392_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
return v___x_3392_;
}
else
{
if (v___x_3392_ == 0)
{
return v___x_3392_;
}
else
{
size_t v___x_3393_; size_t v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = ((size_t)0ULL);
v___x_3394_ = lean_usize_of_nat(v___x_3391_);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3380_, v_vs_3389_, v___x_3393_, v___x_3394_);
return v___x_3395_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(uint8_t v___x_3396_, lean_object* v_as_3397_, size_t v_i_3398_, size_t v_stop_3399_){
_start:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_usize_dec_eq(v_i_3398_, v_stop_3399_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = lean_array_uget_borrowed(v_as_3397_, v_i_3398_);
v___x_3402_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3396_, v___x_3401_);
if (v___x_3402_ == 0)
{
size_t v___x_3403_; size_t v___x_3404_; 
v___x_3403_ = ((size_t)1ULL);
v___x_3404_ = lean_usize_add(v_i_3398_, v___x_3403_);
v_i_3398_ = v___x_3404_;
goto _start;
}
else
{
return v___x_3402_;
}
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = 0;
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5___boxed(lean_object* v___x_3407_, lean_object* v_as_3408_, lean_object* v_i_3409_, lean_object* v_stop_3410_){
_start:
{
uint8_t v___x_1826__boxed_3411_; size_t v_i_boxed_3412_; size_t v_stop_boxed_3413_; uint8_t v_res_3414_; lean_object* v_r_3415_; 
v___x_1826__boxed_3411_ = lean_unbox(v___x_3407_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_stop_boxed_3413_ = lean_unbox_usize(v_stop_3410_);
lean_dec(v_stop_3410_);
v_res_3414_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3_spec__5(v___x_1826__boxed_3411_, v_as_3408_, v_i_boxed_3412_, v_stop_boxed_3413_);
lean_dec_ref(v_as_3408_);
v_r_3415_ = lean_box(v_res_3414_);
return v_r_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3___boxed(lean_object* v___x_3416_, lean_object* v_x_3417_){
_start:
{
uint8_t v___x_1834__boxed_3418_; uint8_t v_res_3419_; lean_object* v_r_3420_; 
v___x_1834__boxed_3418_ = lean_unbox(v___x_3416_);
v_res_3419_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_1834__boxed_3418_, v_x_3417_);
lean_dec_ref(v_x_3417_);
v_r_3420_ = lean_box(v_res_3419_);
return v_r_3420_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(uint8_t v___x_3421_, lean_object* v_t_3422_){
_start:
{
lean_object* v_root_3423_; lean_object* v_tail_3424_; uint8_t v___x_3425_; 
v_root_3423_ = lean_ctor_get(v_t_3422_, 0);
v_tail_3424_ = lean_ctor_get(v_t_3422_, 1);
v___x_3425_ = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__3(v___x_3421_, v_root_3423_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = lean_unsigned_to_nat(0u);
v___x_3427_ = lean_array_get_size(v_tail_3424_);
v___x_3428_ = lean_nat_dec_lt(v___x_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
return v___x_3428_;
}
else
{
if (v___x_3428_ == 0)
{
return v___x_3428_;
}
else
{
size_t v___x_3429_; size_t v___x_3430_; uint8_t v___x_3431_; 
v___x_3429_ = ((size_t)0ULL);
v___x_3430_ = lean_usize_of_nat(v___x_3427_);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1_spec__4(v___x_3421_, v_tail_3424_, v___x_3429_, v___x_3430_);
return v___x_3431_;
}
}
}
else
{
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1___boxed(lean_object* v___x_3432_, lean_object* v_t_3433_){
_start:
{
uint8_t v___x_1877__boxed_3434_; uint8_t v_res_3435_; lean_object* v_r_3436_; 
v___x_1877__boxed_3434_ = lean_unbox(v___x_3432_);
v_res_3435_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_1877__boxed_3434_, v_t_3433_);
lean_dec_ref(v_t_3433_);
v_r_3436_ = lean_box(v_res_3435_);
return v_r_3436_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageLog_hasErrors(lean_object* v_log_3437_){
_start:
{
lean_object* v_reported_3438_; lean_object* v_unreported_3439_; uint8_t v___x_3440_; 
v_reported_3438_ = lean_ctor_get(v_log_3437_, 0);
v_unreported_3439_ = lean_ctor_get(v_log_3437_, 1);
v___x_3440_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__0(v_reported_3438_);
if (v___x_3440_ == 0)
{
uint8_t v___x_3441_; 
v___x_3441_ = l_Lean_PersistentArray_anyM___at___00Lean_MessageLog_hasErrors_spec__1(v___x_3440_, v_unreported_3439_);
return v___x_3441_;
}
else
{
return v___x_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_hasErrors___boxed(lean_object* v_log_3442_){
_start:
{
uint8_t v_res_3443_; lean_object* v_r_3444_; 
v_res_3443_ = l_Lean_MessageLog_hasErrors(v_log_3442_);
lean_dec_ref(v_log_3442_);
v_r_3444_ = lean_box(v_res_3443_);
return v_r_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_markAllReported(lean_object* v_log_3445_){
_start:
{
lean_object* v_reported_3446_; lean_object* v_unreported_3447_; lean_object* v_loggedKinds_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3459_; 
v_reported_3446_ = lean_ctor_get(v_log_3445_, 0);
v_unreported_3447_ = lean_ctor_get(v_log_3445_, 1);
v_loggedKinds_3448_ = lean_ctor_get(v_log_3445_, 2);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_log_3445_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3450_ = v_log_3445_;
v_isShared_3451_ = v_isSharedCheck_3459_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_loggedKinds_3448_);
lean_inc(v_unreported_3447_);
lean_inc(v_reported_3446_);
lean_dec(v_log_3445_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3459_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3452_ = l_Lean_PersistentArray_append___redArg(v_reported_3446_, v_unreported_3447_);
lean_dec_ref(v_unreported_3447_);
v___x_3453_ = lean_unsigned_to_nat(32u);
v___x_3454_ = lean_mk_empty_array_with_capacity(v___x_3453_);
lean_dec_ref(v___x_3454_);
v___x_3455_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 1, v___x_3455_);
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3457_ = v___x_3450_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_loggedKinds_3448_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(size_t v_sz_3460_, size_t v_i_3461_, lean_object* v_bs_3462_){
_start:
{
uint8_t v___x_3463_; 
v___x_3463_ = lean_usize_dec_lt(v_i_3461_, v_sz_3460_);
if (v___x_3463_ == 0)
{
return v_bs_3462_;
}
else
{
lean_object* v_v_3464_; lean_object* v_fileName_3465_; lean_object* v_pos_3466_; lean_object* v_endPos_3467_; uint8_t v_keepFullRange_3468_; uint8_t v_severity_3469_; uint8_t v_isSilent_3470_; lean_object* v_caption_3471_; lean_object* v_data_3472_; lean_object* v___x_3473_; lean_object* v_bs_x27_3474_; lean_object* v___y_3476_; 
v_v_3464_ = lean_array_uget(v_bs_3462_, v_i_3461_);
v_fileName_3465_ = lean_ctor_get(v_v_3464_, 0);
v_pos_3466_ = lean_ctor_get(v_v_3464_, 1);
v_endPos_3467_ = lean_ctor_get(v_v_3464_, 2);
v_keepFullRange_3468_ = lean_ctor_get_uint8(v_v_3464_, sizeof(void*)*5);
v_severity_3469_ = lean_ctor_get_uint8(v_v_3464_, sizeof(void*)*5 + 1);
v_isSilent_3470_ = lean_ctor_get_uint8(v_v_3464_, sizeof(void*)*5 + 2);
v_caption_3471_ = lean_ctor_get(v_v_3464_, 3);
v_data_3472_ = lean_ctor_get(v_v_3464_, 4);
v___x_3473_ = lean_unsigned_to_nat(0u);
v_bs_x27_3474_ = lean_array_uset(v_bs_3462_, v_i_3461_, v___x_3473_);
if (v_severity_3469_ == 2)
{
lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
lean_inc(v_data_3472_);
lean_inc_ref(v_caption_3471_);
lean_inc(v_endPos_3467_);
lean_inc_ref(v_pos_3466_);
lean_inc_ref(v_fileName_3465_);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_v_3464_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; lean_object* v_unused_3490_; lean_object* v_unused_3491_; lean_object* v_unused_3492_; lean_object* v_unused_3493_; 
v_unused_3489_ = lean_ctor_get(v_v_3464_, 4);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_v_3464_, 3);
lean_dec(v_unused_3490_);
v_unused_3491_ = lean_ctor_get(v_v_3464_, 2);
lean_dec(v_unused_3491_);
v_unused_3492_ = lean_ctor_get(v_v_3464_, 1);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_v_3464_, 0);
lean_dec(v_unused_3493_);
v___x_3482_ = v_v_3464_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_dec(v_v_3464_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
uint8_t v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = 1;
if (v_isShared_3483_ == 0)
{
v___x_3486_ = v___x_3482_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_fileName_3465_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_pos_3466_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_endPos_3467_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_caption_3471_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_data_3472_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, sizeof(void*)*5, v_keepFullRange_3468_);
lean_ctor_set_uint8(v_reuseFailAlloc_3487_, sizeof(void*)*5 + 2, v_isSilent_3470_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*5 + 1, v___x_3484_);
v___y_3476_ = v___x_3486_;
goto v___jp_3475_;
}
}
}
else
{
v___y_3476_ = v_v_3464_;
goto v___jp_3475_;
}
v___jp_3475_:
{
size_t v___x_3477_; size_t v___x_3478_; lean_object* v___x_3479_; 
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3461_, v___x_3477_);
v___x_3479_ = lean_array_uset(v_bs_x27_3474_, v_i_3461_, v___y_3476_);
v_i_3461_ = v___x_3478_;
v_bs_3462_ = v___x_3479_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1___boxed(lean_object* v_sz_3494_, lean_object* v_i_3495_, lean_object* v_bs_3496_){
_start:
{
size_t v_sz_boxed_3497_; size_t v_i_boxed_3498_; lean_object* v_res_3499_; 
v_sz_boxed_3497_ = lean_unbox_usize(v_sz_3494_);
lean_dec(v_sz_3494_);
v_i_boxed_3498_ = lean_unbox_usize(v_i_3495_);
lean_dec(v_i_3495_);
v_res_3499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_boxed_3497_, v_i_boxed_3498_, v_bs_3496_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(size_t v_sz_3500_, size_t v_i_3501_, lean_object* v_bs_3502_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_usize_dec_lt(v_i_3501_, v_sz_3500_);
if (v___x_3503_ == 0)
{
return v_bs_3502_;
}
else
{
lean_object* v_v_3504_; lean_object* v___x_3505_; lean_object* v_bs_x27_3506_; lean_object* v___x_3507_; size_t v___x_3508_; size_t v___x_3509_; lean_object* v___x_3510_; 
v_v_3504_ = lean_array_uget(v_bs_3502_, v_i_3501_);
v___x_3505_ = lean_unsigned_to_nat(0u);
v_bs_x27_3506_ = lean_array_uset(v_bs_3502_, v_i_3501_, v___x_3505_);
v___x_3507_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_v_3504_);
v___x_3508_ = ((size_t)1ULL);
v___x_3509_ = lean_usize_add(v_i_3501_, v___x_3508_);
v___x_3510_ = lean_array_uset(v_bs_x27_3506_, v_i_3501_, v___x_3507_);
v_i_3501_ = v___x_3509_;
v_bs_3502_ = v___x_3510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(lean_object* v_x_3512_){
_start:
{
if (lean_obj_tag(v_x_3512_) == 0)
{
lean_object* v_cs_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3523_; 
v_cs_3513_ = lean_ctor_get(v_x_3512_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v_x_3512_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3515_ = v_x_3512_;
v_isShared_3516_ = v_isSharedCheck_3523_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_cs_3513_);
lean_dec(v_x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3523_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
size_t v_sz_3517_; size_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v_sz_3517_ = lean_array_size(v_cs_3513_);
v___x_3518_ = ((size_t)0ULL);
v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_3517_, v___x_3518_, v_cs_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3519_);
v___x_3521_ = v___x_3515_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
else
{
lean_object* v_vs_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3534_; 
v_vs_3524_ = lean_ctor_get(v_x_3512_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_x_3512_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3526_ = v_x_3512_;
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_vs_3524_);
lean_dec(v_x_3512_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3534_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
size_t v_sz_3528_; size_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3532_; 
v_sz_3528_ = lean_array_size(v_vs_3524_);
v___x_3529_ = ((size_t)0ULL);
v___x_3530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3528_, v___x_3529_, v_vs_3524_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3530_);
v___x_3532_ = v___x_3526_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3535_, lean_object* v_i_3536_, lean_object* v_bs_3537_){
_start:
{
size_t v_sz_boxed_3538_; size_t v_i_boxed_3539_; lean_object* v_res_3540_; 
v_sz_boxed_3538_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v_i_boxed_3539_ = lean_unbox_usize(v_i_3536_);
lean_dec(v_i_3536_);
v_res_3540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0_spec__1(v_sz_boxed_3538_, v_i_boxed_3539_, v_bs_3537_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(lean_object* v_t_3541_){
_start:
{
lean_object* v_root_3542_; lean_object* v_tail_3543_; lean_object* v_size_3544_; size_t v_shift_3545_; lean_object* v_tailOff_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3557_; 
v_root_3542_ = lean_ctor_get(v_t_3541_, 0);
v_tail_3543_ = lean_ctor_get(v_t_3541_, 1);
v_size_3544_ = lean_ctor_get(v_t_3541_, 2);
v_shift_3545_ = lean_ctor_get_usize(v_t_3541_, 4);
v_tailOff_3546_ = lean_ctor_get(v_t_3541_, 3);
v_isSharedCheck_3557_ = !lean_is_exclusive(v_t_3541_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3548_ = v_t_3541_;
v_isShared_3549_ = v_isSharedCheck_3557_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_tailOff_3546_);
lean_inc(v_size_3544_);
lean_inc(v_tail_3543_);
lean_inc(v_root_3542_);
lean_dec(v_t_3541_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3557_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; size_t v_sz_3551_; size_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3550_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__0(v_root_3542_);
v_sz_3551_ = lean_array_size(v_tail_3543_);
v___x_3552_ = ((size_t)0ULL);
v___x_3553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0_spec__1(v_sz_3551_, v___x_3552_, v_tail_3543_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 1, v___x_3553_);
lean_ctor_set(v___x_3548_, 0, v___x_3550_);
v___x_3555_ = v___x_3548_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_size_3544_);
lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_tailOff_3546_);
lean_ctor_set_usize(v_reuseFailAlloc_3556_, 4, v_shift_3545_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToWarnings(lean_object* v_log_3558_){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v_unreported_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3571_; 
v___x_3559_ = lean_unsigned_to_nat(32u);
v___x_3560_ = lean_mk_empty_array_with_capacity(v___x_3559_);
lean_dec_ref(v___x_3560_);
v___x_3561_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3562_ = lean_ctor_get(v_log_3558_, 1);
v_isSharedCheck_3571_ = !lean_is_exclusive(v_log_3558_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; lean_object* v_unused_3573_; 
v_unused_3572_ = lean_ctor_get(v_log_3558_, 2);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_log_3558_, 0);
lean_dec(v_unused_3573_);
v___x_3564_ = v_log_3558_;
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_unreported_3562_);
lean_dec(v_log_3558_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3566_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToWarnings_spec__0(v_unreported_3562_);
v___x_3567_ = l_Lean_NameSet_empty;
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 2, v___x_3567_);
lean_ctor_set(v___x_3564_, 1, v___x_3566_);
lean_ctor_set(v___x_3564_, 0, v___x_3561_);
v___x_3569_ = v___x_3564_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(size_t v_sz_3574_, size_t v_i_3575_, lean_object* v_bs_3576_){
_start:
{
uint8_t v___x_3577_; 
v___x_3577_ = lean_usize_dec_lt(v_i_3575_, v_sz_3574_);
if (v___x_3577_ == 0)
{
return v_bs_3576_;
}
else
{
lean_object* v_v_3578_; lean_object* v_fileName_3579_; lean_object* v_pos_3580_; lean_object* v_endPos_3581_; uint8_t v_keepFullRange_3582_; uint8_t v_severity_3583_; uint8_t v_isSilent_3584_; lean_object* v_caption_3585_; lean_object* v_data_3586_; lean_object* v___x_3587_; lean_object* v_bs_x27_3588_; lean_object* v___y_3590_; 
v_v_3578_ = lean_array_uget(v_bs_3576_, v_i_3575_);
v_fileName_3579_ = lean_ctor_get(v_v_3578_, 0);
v_pos_3580_ = lean_ctor_get(v_v_3578_, 1);
v_endPos_3581_ = lean_ctor_get(v_v_3578_, 2);
v_keepFullRange_3582_ = lean_ctor_get_uint8(v_v_3578_, sizeof(void*)*5);
v_severity_3583_ = lean_ctor_get_uint8(v_v_3578_, sizeof(void*)*5 + 1);
v_isSilent_3584_ = lean_ctor_get_uint8(v_v_3578_, sizeof(void*)*5 + 2);
v_caption_3585_ = lean_ctor_get(v_v_3578_, 3);
v_data_3586_ = lean_ctor_get(v_v_3578_, 4);
v___x_3587_ = lean_unsigned_to_nat(0u);
v_bs_x27_3588_ = lean_array_uset(v_bs_3576_, v_i_3575_, v___x_3587_);
if (v_severity_3583_ == 2)
{
lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3602_; 
lean_inc(v_data_3586_);
lean_inc_ref(v_caption_3585_);
lean_inc(v_endPos_3581_);
lean_inc_ref(v_pos_3580_);
lean_inc_ref(v_fileName_3579_);
v_isSharedCheck_3602_ = !lean_is_exclusive(v_v_3578_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; lean_object* v_unused_3607_; 
v_unused_3603_ = lean_ctor_get(v_v_3578_, 4);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_v_3578_, 3);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_v_3578_, 2);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_v_3578_, 1);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_v_3578_, 0);
lean_dec(v_unused_3607_);
v___x_3596_ = v_v_3578_;
v_isShared_3597_ = v_isSharedCheck_3602_;
goto v_resetjp_3595_;
}
else
{
lean_dec(v_v_3578_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3602_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
uint8_t v___x_3598_; lean_object* v___x_3600_; 
v___x_3598_ = 0;
if (v_isShared_3597_ == 0)
{
v___x_3600_ = v___x_3596_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_fileName_3579_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_pos_3580_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_endPos_3581_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_caption_3585_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_data_3586_);
lean_ctor_set_uint8(v_reuseFailAlloc_3601_, sizeof(void*)*5, v_keepFullRange_3582_);
lean_ctor_set_uint8(v_reuseFailAlloc_3601_, sizeof(void*)*5 + 2, v_isSilent_3584_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_ctor_set_uint8(v___x_3600_, sizeof(void*)*5 + 1, v___x_3598_);
v___y_3590_ = v___x_3600_;
goto v___jp_3589_;
}
}
}
else
{
v___y_3590_ = v_v_3578_;
goto v___jp_3589_;
}
v___jp_3589_:
{
size_t v___x_3591_; size_t v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = ((size_t)1ULL);
v___x_3592_ = lean_usize_add(v_i_3575_, v___x_3591_);
v___x_3593_ = lean_array_uset(v_bs_x27_3588_, v_i_3575_, v___y_3590_);
v_i_3575_ = v___x_3592_;
v_bs_3576_ = v___x_3593_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1___boxed(lean_object* v_sz_3608_, lean_object* v_i_3609_, lean_object* v_bs_3610_){
_start:
{
size_t v_sz_boxed_3611_; size_t v_i_boxed_3612_; lean_object* v_res_3613_; 
v_sz_boxed_3611_ = lean_unbox_usize(v_sz_3608_);
lean_dec(v_sz_3608_);
v_i_boxed_3612_ = lean_unbox_usize(v_i_3609_);
lean_dec(v_i_3609_);
v_res_3613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_boxed_3611_, v_i_boxed_3612_, v_bs_3610_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(size_t v_sz_3614_, size_t v_i_3615_, lean_object* v_bs_3616_){
_start:
{
uint8_t v___x_3617_; 
v___x_3617_ = lean_usize_dec_lt(v_i_3615_, v_sz_3614_);
if (v___x_3617_ == 0)
{
return v_bs_3616_;
}
else
{
lean_object* v_v_3618_; lean_object* v___x_3619_; lean_object* v_bs_x27_3620_; lean_object* v___x_3621_; size_t v___x_3622_; size_t v___x_3623_; lean_object* v___x_3624_; 
v_v_3618_ = lean_array_uget(v_bs_3616_, v_i_3615_);
v___x_3619_ = lean_unsigned_to_nat(0u);
v_bs_x27_3620_ = lean_array_uset(v_bs_3616_, v_i_3615_, v___x_3619_);
v___x_3621_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_v_3618_);
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3615_, v___x_3622_);
v___x_3624_ = lean_array_uset(v_bs_x27_3620_, v_i_3615_, v___x_3621_);
v_i_3615_ = v___x_3623_;
v_bs_3616_ = v___x_3624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(lean_object* v_x_3626_){
_start:
{
if (lean_obj_tag(v_x_3626_) == 0)
{
lean_object* v_cs_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3637_; 
v_cs_3627_ = lean_ctor_get(v_x_3626_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_x_3626_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3629_ = v_x_3626_;
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_cs_3627_);
lean_dec(v_x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3637_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
size_t v_sz_3631_; size_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3635_; 
v_sz_3631_ = lean_array_size(v_cs_3627_);
v___x_3632_ = ((size_t)0ULL);
v___x_3633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_3631_, v___x_3632_, v_cs_3627_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3633_);
v___x_3635_ = v___x_3629_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
else
{
lean_object* v_vs_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3648_; 
v_vs_3638_ = lean_ctor_get(v_x_3626_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_x_3626_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3640_ = v_x_3626_;
v_isShared_3641_ = v_isSharedCheck_3648_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_vs_3638_);
lean_dec(v_x_3626_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3648_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
size_t v_sz_3642_; size_t v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v_sz_3642_ = lean_array_size(v_vs_3638_);
v___x_3643_ = ((size_t)0ULL);
v___x_3644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3642_, v___x_3643_, v_vs_3638_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3644_);
v___x_3646_ = v___x_3640_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1___boxed(lean_object* v_sz_3649_, lean_object* v_i_3650_, lean_object* v_bs_3651_){
_start:
{
size_t v_sz_boxed_3652_; size_t v_i_boxed_3653_; lean_object* v_res_3654_; 
v_sz_boxed_3652_ = lean_unbox_usize(v_sz_3649_);
lean_dec(v_sz_3649_);
v_i_boxed_3653_ = lean_unbox_usize(v_i_3650_);
lean_dec(v_i_3650_);
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0_spec__1(v_sz_boxed_3652_, v_i_boxed_3653_, v_bs_3651_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(lean_object* v_t_3655_){
_start:
{
lean_object* v_root_3656_; lean_object* v_tail_3657_; lean_object* v_size_3658_; size_t v_shift_3659_; lean_object* v_tailOff_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3671_; 
v_root_3656_ = lean_ctor_get(v_t_3655_, 0);
v_tail_3657_ = lean_ctor_get(v_t_3655_, 1);
v_size_3658_ = lean_ctor_get(v_t_3655_, 2);
v_shift_3659_ = lean_ctor_get_usize(v_t_3655_, 4);
v_tailOff_3660_ = lean_ctor_get(v_t_3655_, 3);
v_isSharedCheck_3671_ = !lean_is_exclusive(v_t_3655_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3662_ = v_t_3655_;
v_isShared_3663_ = v_isSharedCheck_3671_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_tailOff_3660_);
lean_inc(v_size_3658_);
lean_inc(v_tail_3657_);
lean_inc(v_root_3656_);
lean_dec(v_t_3655_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3671_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; size_t v_sz_3665_; size_t v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3669_; 
v___x_3664_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__0(v_root_3656_);
v_sz_3665_ = lean_array_size(v_tail_3657_);
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0_spec__1(v_sz_3665_, v___x_3666_, v_tail_3657_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v___x_3667_);
lean_ctor_set(v___x_3662_, 0, v___x_3664_);
v___x_3669_ = v___x_3662_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_size_3658_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_tailOff_3660_);
lean_ctor_set_usize(v_reuseFailAlloc_3670_, 4, v_shift_3659_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_errorsToInfos(lean_object* v_log_3672_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v_unreported_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3685_; 
v___x_3673_ = lean_unsigned_to_nat(32u);
v___x_3674_ = lean_mk_empty_array_with_capacity(v___x_3673_);
lean_dec_ref(v___x_3674_);
v___x_3675_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3676_ = lean_ctor_get(v_log_3672_, 1);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_log_3672_);
if (v_isSharedCheck_3685_ == 0)
{
lean_object* v_unused_3686_; lean_object* v_unused_3687_; 
v_unused_3686_ = lean_ctor_get(v_log_3672_, 2);
lean_dec(v_unused_3686_);
v_unused_3687_ = lean_ctor_get(v_log_3672_, 0);
lean_dec(v_unused_3687_);
v___x_3678_ = v_log_3672_;
v_isShared_3679_ = v_isSharedCheck_3685_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_unreported_3676_);
lean_dec(v_log_3672_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3685_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3680_ = l_Lean_PersistentArray_mapM___at___00Lean_MessageLog_errorsToInfos_spec__0(v_unreported_3676_);
v___x_3681_ = l_Lean_NameSet_empty;
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 2, v___x_3681_);
lean_ctor_set(v___x_3678_, 1, v___x_3680_);
lean_ctor_set(v___x_3678_, 0, v___x_3675_);
v___x_3683_ = v___x_3678_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___x_3680_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(lean_object* v_as_3688_, size_t v_i_3689_, size_t v_stop_3690_, lean_object* v_b_3691_){
_start:
{
lean_object* v___y_3693_; uint8_t v___x_3697_; 
v___x_3697_ = lean_usize_dec_eq(v_i_3689_, v_stop_3690_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; uint8_t v_severity_3699_; 
v___x_3698_ = lean_array_uget_borrowed(v_as_3688_, v_i_3689_);
v_severity_3699_ = lean_ctor_get_uint8(v___x_3698_, sizeof(void*)*5 + 1);
if (v_severity_3699_ == 0)
{
lean_object* v___x_3700_; 
lean_inc(v___x_3698_);
v___x_3700_ = l_Lean_PersistentArray_push___redArg(v_b_3691_, v___x_3698_);
v___y_3693_ = v___x_3700_;
goto v___jp_3692_;
}
else
{
v___y_3693_ = v_b_3691_;
goto v___jp_3692_;
}
}
else
{
return v_b_3691_;
}
v___jp_3692_:
{
size_t v___x_3694_; size_t v___x_3695_; 
v___x_3694_ = ((size_t)1ULL);
v___x_3695_ = lean_usize_add(v_i_3689_, v___x_3694_);
v_i_3689_ = v___x_3695_;
v_b_3691_ = v___y_3693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1___boxed(lean_object* v_as_3701_, lean_object* v_i_3702_, lean_object* v_stop_3703_, lean_object* v_b_3704_){
_start:
{
size_t v_i_boxed_3705_; size_t v_stop_boxed_3706_; lean_object* v_res_3707_; 
v_i_boxed_3705_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_stop_boxed_3706_ = lean_unbox_usize(v_stop_3703_);
lean_dec(v_stop_3703_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_as_3701_, v_i_boxed_3705_, v_stop_boxed_3706_, v_b_3704_);
lean_dec_ref(v_as_3701_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(lean_object* v_x_3708_, lean_object* v_x_3709_){
_start:
{
if (lean_obj_tag(v_x_3708_) == 0)
{
lean_object* v_cs_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v_cs_3710_ = lean_ctor_get(v_x_3708_, 0);
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v_cs_3710_);
v___x_3713_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
return v_x_3709_;
}
else
{
size_t v___x_3714_; size_t v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = lean_usize_of_nat(v___x_3712_);
v___x_3716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3710_, v___x_3714_, v___x_3715_, v_x_3709_);
return v___x_3716_;
}
}
else
{
lean_object* v_vs_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_vs_3717_ = lean_ctor_get(v_x_3708_, 0);
v___x_3718_ = lean_unsigned_to_nat(0u);
v___x_3719_ = lean_array_get_size(v_vs_3717_);
v___x_3720_ = lean_nat_dec_lt(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
return v_x_3709_;
}
else
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = ((size_t)0ULL);
v___x_3722_ = lean_usize_of_nat(v___x_3719_);
v___x_3723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3717_, v___x_3721_, v___x_3722_, v_x_3709_);
return v___x_3723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(lean_object* v_as_3724_, size_t v_i_3725_, size_t v_stop_3726_, lean_object* v_b_3727_){
_start:
{
uint8_t v___x_3728_; 
v___x_3728_ = lean_usize_dec_eq(v_i_3725_, v_stop_3726_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; size_t v___x_3731_; size_t v___x_3732_; 
v___x_3729_ = lean_array_uget_borrowed(v_as_3724_, v_i_3725_);
v___x_3730_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v___x_3729_, v_b_3727_);
v___x_3731_ = ((size_t)1ULL);
v___x_3732_ = lean_usize_add(v_i_3725_, v___x_3731_);
v_i_3725_ = v___x_3732_;
v_b_3727_ = v___x_3730_;
goto _start;
}
else
{
return v_b_3727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3734_, lean_object* v_i_3735_, lean_object* v_stop_3736_, lean_object* v_b_3737_){
_start:
{
size_t v_i_boxed_3738_; size_t v_stop_boxed_3739_; lean_object* v_res_3740_; 
v_i_boxed_3738_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_stop_boxed_3739_ = lean_unbox_usize(v_stop_3736_);
lean_dec(v_stop_3736_);
v_res_3740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_as_3734_, v_i_boxed_3738_, v_stop_boxed_3739_, v_b_3737_);
lean_dec_ref(v_as_3734_);
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2___boxed(lean_object* v_x_3741_, lean_object* v_x_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_x_3741_, v_x_3742_);
lean_dec_ref(v_x_3741_);
return v_res_3743_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(lean_object* v_x_3745_, size_t v_x_3746_, size_t v_x_3747_, lean_object* v_x_3748_){
_start:
{
if (lean_obj_tag(v_x_3745_) == 0)
{
lean_object* v_cs_3749_; lean_object* v___x_3750_; size_t v___x_3751_; lean_object* v_j_3752_; lean_object* v___x_3753_; size_t v___x_3754_; size_t v___x_3755_; size_t v___x_3756_; size_t v___x_3757_; size_t v___x_3758_; size_t v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_cs_3749_ = lean_ctor_get(v_x_3745_, 0);
v___x_3750_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3751_ = lean_usize_shift_right(v_x_3746_, v_x_3747_);
v_j_3752_ = lean_usize_to_nat(v___x_3751_);
v___x_3753_ = lean_array_get_borrowed(v___x_3750_, v_cs_3749_, v_j_3752_);
v___x_3754_ = ((size_t)1ULL);
v___x_3755_ = lean_usize_shift_left(v___x_3754_, v_x_3747_);
v___x_3756_ = lean_usize_sub(v___x_3755_, v___x_3754_);
v___x_3757_ = lean_usize_land(v_x_3746_, v___x_3756_);
v___x_3758_ = ((size_t)5ULL);
v___x_3759_ = lean_usize_sub(v_x_3747_, v___x_3758_);
v___x_3760_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v___x_3753_, v___x_3757_, v___x_3759_, v_x_3748_);
v___x_3761_ = lean_unsigned_to_nat(1u);
v___x_3762_ = lean_nat_add(v_j_3752_, v___x_3761_);
lean_dec(v_j_3752_);
v___x_3763_ = lean_array_get_size(v_cs_3749_);
v___x_3764_ = lean_nat_dec_lt(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_dec(v___x_3762_);
return v___x_3760_;
}
else
{
size_t v___x_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = lean_usize_of_nat(v___x_3762_);
lean_dec(v___x_3762_);
v___x_3766_ = lean_usize_of_nat(v___x_3763_);
v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0_spec__1(v_cs_3749_, v___x_3765_, v___x_3766_, v___x_3760_);
return v___x_3767_;
}
}
else
{
lean_object* v_vs_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_vs_3768_ = lean_ctor_get(v_x_3745_, 0);
v___x_3769_ = lean_usize_to_nat(v_x_3746_);
v___x_3770_ = lean_array_get_size(v_vs_3768_);
v___x_3771_ = lean_nat_dec_lt(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec(v___x_3769_);
return v_x_3748_;
}
else
{
size_t v___x_3772_; size_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_usize_of_nat(v___x_3769_);
lean_dec(v___x_3769_);
v___x_3773_ = lean_usize_of_nat(v___x_3770_);
v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_vs_3768_, v___x_3772_, v___x_3773_, v_x_3748_);
return v___x_3774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___boxed(lean_object* v_x_3775_, lean_object* v_x_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
size_t v_x_1153__boxed_3779_; size_t v_x_1154__boxed_3780_; lean_object* v_res_3781_; 
v_x_1153__boxed_3779_ = lean_unbox_usize(v_x_3776_);
lean_dec(v_x_3776_);
v_x_1154__boxed_3780_ = lean_unbox_usize(v_x_3777_);
lean_dec(v_x_3777_);
v_res_3781_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_x_3775_, v_x_1153__boxed_3779_, v_x_1154__boxed_3780_, v_x_3778_);
lean_dec_ref(v_x_3775_);
return v_res_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(lean_object* v_t_3782_, lean_object* v_init_3783_, lean_object* v_start_3784_){
_start:
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = lean_nat_dec_eq(v_start_3784_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v_root_3787_; lean_object* v_tail_3788_; size_t v_shift_3789_; lean_object* v_tailOff_3790_; uint8_t v___x_3791_; 
v_root_3787_ = lean_ctor_get(v_t_3782_, 0);
v_tail_3788_ = lean_ctor_get(v_t_3782_, 1);
v_shift_3789_ = lean_ctor_get_usize(v_t_3782_, 4);
v_tailOff_3790_ = lean_ctor_get(v_t_3782_, 3);
v___x_3791_ = lean_nat_dec_le(v_tailOff_3790_, v_start_3784_);
if (v___x_3791_ == 0)
{
size_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; uint8_t v___x_3795_; 
v___x_3792_ = lean_usize_of_nat(v_start_3784_);
v___x_3793_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0(v_root_3787_, v___x_3792_, v_shift_3789_, v_init_3783_);
v___x_3794_ = lean_array_get_size(v_tail_3788_);
v___x_3795_ = lean_nat_dec_lt(v___x_3785_, v___x_3794_);
if (v___x_3795_ == 0)
{
return v___x_3793_;
}
else
{
size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = lean_usize_of_nat(v___x_3794_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3788_, v___x_3796_, v___x_3797_, v___x_3793_);
return v___x_3798_;
}
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = lean_nat_sub(v_start_3784_, v_tailOff_3790_);
v___x_3800_ = lean_array_get_size(v_tail_3788_);
v___x_3801_ = lean_nat_dec_lt(v___x_3799_, v___x_3800_);
if (v___x_3801_ == 0)
{
lean_dec(v___x_3799_);
return v_init_3783_;
}
else
{
size_t v___x_3802_; size_t v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_usize_of_nat(v___x_3799_);
lean_dec(v___x_3799_);
v___x_3803_ = lean_usize_of_nat(v___x_3800_);
v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3788_, v___x_3802_, v___x_3803_, v_init_3783_);
return v___x_3804_;
}
}
}
else
{
lean_object* v_root_3805_; lean_object* v_tail_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_root_3805_ = lean_ctor_get(v_t_3782_, 0);
v_tail_3806_ = lean_ctor_get(v_t_3782_, 1);
v___x_3807_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__2(v_root_3805_, v_init_3783_);
v___x_3808_ = lean_array_get_size(v_tail_3806_);
v___x_3809_ = lean_nat_dec_lt(v___x_3785_, v___x_3808_);
if (v___x_3809_ == 0)
{
return v___x_3807_;
}
else
{
size_t v___x_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = ((size_t)0ULL);
v___x_3811_ = lean_usize_of_nat(v___x_3808_);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__1(v_tail_3806_, v___x_3810_, v___x_3811_, v___x_3807_);
return v___x_3812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0___boxed(lean_object* v_t_3813_, lean_object* v_init_3814_, lean_object* v_start_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_t_3813_, v_init_3814_, v_start_3815_);
lean_dec(v_start_3815_);
lean_dec_ref(v_t_3813_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getInfoMessages(lean_object* v_log_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v_unreported_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3831_; 
v___x_3818_ = lean_unsigned_to_nat(32u);
v___x_3819_ = lean_mk_empty_array_with_capacity(v___x_3818_);
lean_dec_ref(v___x_3819_);
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3822_ = lean_ctor_get(v_log_3817_, 1);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_log_3817_);
if (v_isSharedCheck_3831_ == 0)
{
lean_object* v_unused_3832_; lean_object* v_unused_3833_; 
v_unused_3832_ = lean_ctor_get(v_log_3817_, 2);
lean_dec(v_unused_3832_);
v_unused_3833_ = lean_ctor_get(v_log_3817_, 0);
lean_dec(v_unused_3833_);
v___x_3824_ = v_log_3817_;
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_unreported_3822_);
lean_dec(v_log_3817_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3831_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3826_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0(v_unreported_3822_, v___x_3821_, v___x_3820_);
lean_dec_ref(v_unreported_3822_);
v___x_3827_ = l_Lean_NameSet_empty;
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 2, v___x_3827_);
lean_ctor_set(v___x_3824_, 1, v___x_3826_);
lean_ctor_set(v___x_3824_, 0, v___x_3821_);
v___x_3829_ = v___x_3824_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(lean_object* v_as_3834_, size_t v_i_3835_, size_t v_stop_3836_, lean_object* v_b_3837_){
_start:
{
lean_object* v___y_3839_; uint8_t v___x_3843_; 
v___x_3843_ = lean_usize_dec_eq(v_i_3835_, v_stop_3836_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; uint8_t v_severity_3845_; 
v___x_3844_ = lean_array_uget_borrowed(v_as_3834_, v_i_3835_);
v_severity_3845_ = lean_ctor_get_uint8(v___x_3844_, sizeof(void*)*5 + 1);
if (v_severity_3845_ == 1)
{
lean_object* v___x_3846_; 
lean_inc(v___x_3844_);
v___x_3846_ = l_Lean_PersistentArray_push___redArg(v_b_3837_, v___x_3844_);
v___y_3839_ = v___x_3846_;
goto v___jp_3838_;
}
else
{
v___y_3839_ = v_b_3837_;
goto v___jp_3838_;
}
}
else
{
return v_b_3837_;
}
v___jp_3838_:
{
size_t v___x_3840_; size_t v___x_3841_; 
v___x_3840_ = ((size_t)1ULL);
v___x_3841_ = lean_usize_add(v_i_3835_, v___x_3840_);
v_i_3835_ = v___x_3841_;
v_b_3837_ = v___y_3839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1___boxed(lean_object* v_as_3847_, lean_object* v_i_3848_, lean_object* v_stop_3849_, lean_object* v_b_3850_){
_start:
{
size_t v_i_boxed_3851_; size_t v_stop_boxed_3852_; lean_object* v_res_3853_; 
v_i_boxed_3851_ = lean_unbox_usize(v_i_3848_);
lean_dec(v_i_3848_);
v_stop_boxed_3852_ = lean_unbox_usize(v_stop_3849_);
lean_dec(v_stop_3849_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_as_3847_, v_i_boxed_3851_, v_stop_boxed_3852_, v_b_3850_);
lean_dec_ref(v_as_3847_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(lean_object* v_x_3854_, lean_object* v_x_3855_){
_start:
{
if (lean_obj_tag(v_x_3854_) == 0)
{
lean_object* v_cs_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_cs_3856_ = lean_ctor_get(v_x_3854_, 0);
v___x_3857_ = lean_unsigned_to_nat(0u);
v___x_3858_ = lean_array_get_size(v_cs_3856_);
v___x_3859_ = lean_nat_dec_lt(v___x_3857_, v___x_3858_);
if (v___x_3859_ == 0)
{
return v_x_3855_;
}
else
{
size_t v___x_3860_; size_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3860_ = ((size_t)0ULL);
v___x_3861_ = lean_usize_of_nat(v___x_3858_);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3856_, v___x_3860_, v___x_3861_, v_x_3855_);
return v___x_3862_;
}
}
else
{
lean_object* v_vs_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v_vs_3863_ = lean_ctor_get(v_x_3854_, 0);
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_array_get_size(v_vs_3863_);
v___x_3866_ = lean_nat_dec_lt(v___x_3864_, v___x_3865_);
if (v___x_3866_ == 0)
{
return v_x_3855_;
}
else
{
size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3867_ = ((size_t)0ULL);
v___x_3868_ = lean_usize_of_nat(v___x_3865_);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3863_, v___x_3867_, v___x_3868_, v_x_3855_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(lean_object* v_as_3870_, size_t v_i_3871_, size_t v_stop_3872_, lean_object* v_b_3873_){
_start:
{
uint8_t v___x_3874_; 
v___x_3874_ = lean_usize_dec_eq(v_i_3871_, v_stop_3872_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; lean_object* v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; 
v___x_3875_ = lean_array_uget_borrowed(v_as_3870_, v_i_3871_);
v___x_3876_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v___x_3875_, v_b_3873_);
v___x_3877_ = ((size_t)1ULL);
v___x_3878_ = lean_usize_add(v_i_3871_, v___x_3877_);
v_i_3871_ = v___x_3878_;
v_b_3873_ = v___x_3876_;
goto _start;
}
else
{
return v_b_3873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1___boxed(lean_object* v_as_3880_, lean_object* v_i_3881_, lean_object* v_stop_3882_, lean_object* v_b_3883_){
_start:
{
size_t v_i_boxed_3884_; size_t v_stop_boxed_3885_; lean_object* v_res_3886_; 
v_i_boxed_3884_ = lean_unbox_usize(v_i_3881_);
lean_dec(v_i_3881_);
v_stop_boxed_3885_ = lean_unbox_usize(v_stop_3882_);
lean_dec(v_stop_3882_);
v_res_3886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_as_3880_, v_i_boxed_3884_, v_stop_boxed_3885_, v_b_3883_);
lean_dec_ref(v_as_3880_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2___boxed(lean_object* v_x_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_x_3887_, v_x_3888_);
lean_dec_ref(v_x_3887_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(lean_object* v_x_3890_, size_t v_x_3891_, size_t v_x_3892_, lean_object* v_x_3893_){
_start:
{
if (lean_obj_tag(v_x_3890_) == 0)
{
lean_object* v_cs_3894_; lean_object* v___x_3895_; size_t v___x_3896_; lean_object* v_j_3897_; lean_object* v___x_3898_; size_t v___x_3899_; size_t v___x_3900_; size_t v___x_3901_; size_t v___x_3902_; size_t v___x_3903_; size_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; uint8_t v___x_3909_; 
v_cs_3894_ = lean_ctor_get(v_x_3890_, 0);
v___x_3895_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getInfoMessages_spec__0_spec__0___closed__0);
v___x_3896_ = lean_usize_shift_right(v_x_3891_, v_x_3892_);
v_j_3897_ = lean_usize_to_nat(v___x_3896_);
v___x_3898_ = lean_array_get_borrowed(v___x_3895_, v_cs_3894_, v_j_3897_);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_shift_left(v___x_3899_, v_x_3892_);
v___x_3901_ = lean_usize_sub(v___x_3900_, v___x_3899_);
v___x_3902_ = lean_usize_land(v_x_3891_, v___x_3901_);
v___x_3903_ = ((size_t)5ULL);
v___x_3904_ = lean_usize_sub(v_x_3892_, v___x_3903_);
v___x_3905_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v___x_3898_, v___x_3902_, v___x_3904_, v_x_3893_);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = lean_nat_add(v_j_3897_, v___x_3906_);
lean_dec(v_j_3897_);
v___x_3908_ = lean_array_get_size(v_cs_3894_);
v___x_3909_ = lean_nat_dec_lt(v___x_3907_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_dec(v___x_3907_);
return v___x_3905_;
}
else
{
size_t v___x_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_usize_of_nat(v___x_3907_);
lean_dec(v___x_3907_);
v___x_3911_ = lean_usize_of_nat(v___x_3908_);
v___x_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0_spec__1(v_cs_3894_, v___x_3910_, v___x_3911_, v___x_3905_);
return v___x_3912_;
}
}
else
{
lean_object* v_vs_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; 
v_vs_3913_ = lean_ctor_get(v_x_3890_, 0);
v___x_3914_ = lean_usize_to_nat(v_x_3891_);
v___x_3915_ = lean_array_get_size(v_vs_3913_);
v___x_3916_ = lean_nat_dec_lt(v___x_3914_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_dec(v___x_3914_);
return v_x_3893_;
}
else
{
size_t v___x_3917_; size_t v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_usize_of_nat(v___x_3914_);
lean_dec(v___x_3914_);
v___x_3918_ = lean_usize_of_nat(v___x_3915_);
v___x_3919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_vs_3913_, v___x_3917_, v___x_3918_, v_x_3893_);
return v___x_3919_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0___boxed(lean_object* v_x_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_){
_start:
{
size_t v_x_1152__boxed_3924_; size_t v_x_1153__boxed_3925_; lean_object* v_res_3926_; 
v_x_1152__boxed_3924_ = lean_unbox_usize(v_x_3921_);
lean_dec(v_x_3921_);
v_x_1153__boxed_3925_ = lean_unbox_usize(v_x_3922_);
lean_dec(v_x_3922_);
v_res_3926_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_x_3920_, v_x_1152__boxed_3924_, v_x_1153__boxed_3925_, v_x_3923_);
lean_dec_ref(v_x_3920_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(lean_object* v_t_3927_, lean_object* v_init_3928_, lean_object* v_start_3929_){
_start:
{
lean_object* v___x_3930_; uint8_t v___x_3931_; 
v___x_3930_ = lean_unsigned_to_nat(0u);
v___x_3931_ = lean_nat_dec_eq(v_start_3929_, v___x_3930_);
if (v___x_3931_ == 0)
{
lean_object* v_root_3932_; lean_object* v_tail_3933_; size_t v_shift_3934_; lean_object* v_tailOff_3935_; uint8_t v___x_3936_; 
v_root_3932_ = lean_ctor_get(v_t_3927_, 0);
v_tail_3933_ = lean_ctor_get(v_t_3927_, 1);
v_shift_3934_ = lean_ctor_get_usize(v_t_3927_, 4);
v_tailOff_3935_ = lean_ctor_get(v_t_3927_, 3);
v___x_3936_ = lean_nat_dec_le(v_tailOff_3935_, v_start_3929_);
if (v___x_3936_ == 0)
{
size_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; 
v___x_3937_ = lean_usize_of_nat(v_start_3929_);
v___x_3938_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__0(v_root_3932_, v___x_3937_, v_shift_3934_, v_init_3928_);
v___x_3939_ = lean_array_get_size(v_tail_3933_);
v___x_3940_ = lean_nat_dec_lt(v___x_3930_, v___x_3939_);
if (v___x_3940_ == 0)
{
return v___x_3938_;
}
else
{
size_t v___x_3941_; size_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = ((size_t)0ULL);
v___x_3942_ = lean_usize_of_nat(v___x_3939_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3933_, v___x_3941_, v___x_3942_, v___x_3938_);
return v___x_3943_;
}
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_nat_sub(v_start_3929_, v_tailOff_3935_);
v___x_3945_ = lean_array_get_size(v_tail_3933_);
v___x_3946_ = lean_nat_dec_lt(v___x_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_dec(v___x_3944_);
return v_init_3928_;
}
else
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = lean_usize_of_nat(v___x_3944_);
lean_dec(v___x_3944_);
v___x_3948_ = lean_usize_of_nat(v___x_3945_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3933_, v___x_3947_, v___x_3948_, v_init_3928_);
return v___x_3949_;
}
}
}
else
{
lean_object* v_root_3950_; lean_object* v_tail_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v_root_3950_ = lean_ctor_get(v_t_3927_, 0);
v_tail_3951_ = lean_ctor_get(v_t_3927_, 1);
v___x_3952_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__2(v_root_3950_, v_init_3928_);
v___x_3953_ = lean_array_get_size(v_tail_3951_);
v___x_3954_ = lean_nat_dec_lt(v___x_3930_, v___x_3953_);
if (v___x_3954_ == 0)
{
return v___x_3952_;
}
else
{
size_t v___x_3955_; size_t v___x_3956_; lean_object* v___x_3957_; 
v___x_3955_ = ((size_t)0ULL);
v___x_3956_ = lean_usize_of_nat(v___x_3953_);
v___x_3957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0_spec__1(v_tail_3951_, v___x_3955_, v___x_3956_, v___x_3952_);
return v___x_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0___boxed(lean_object* v_t_3958_, lean_object* v_init_3959_, lean_object* v_start_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_t_3958_, v_init_3959_, v_start_3960_);
lean_dec(v_start_3960_);
lean_dec_ref(v_t_3958_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_getWarningMessages(lean_object* v_log_3962_){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_unreported_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3976_; 
v___x_3963_ = lean_unsigned_to_nat(32u);
v___x_3964_ = lean_mk_empty_array_with_capacity(v___x_3963_);
lean_dec_ref(v___x_3964_);
v___x_3965_ = lean_unsigned_to_nat(0u);
v___x_3966_ = lean_obj_once(&l_Lean_instInhabitedMessageLog_default___closed__1, &l_Lean_instInhabitedMessageLog_default___closed__1_once, _init_l_Lean_instInhabitedMessageLog_default___closed__1);
v_unreported_3967_ = lean_ctor_get(v_log_3962_, 1);
v_isSharedCheck_3976_ = !lean_is_exclusive(v_log_3962_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; lean_object* v_unused_3978_; 
v_unused_3977_ = lean_ctor_get(v_log_3962_, 2);
lean_dec(v_unused_3977_);
v_unused_3978_ = lean_ctor_get(v_log_3962_, 0);
lean_dec(v_unused_3978_);
v___x_3969_ = v_log_3962_;
v_isShared_3970_ = v_isSharedCheck_3976_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_unreported_3967_);
lean_dec(v_log_3962_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3976_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3971_ = l_Lean_PersistentArray_foldlM___at___00Lean_MessageLog_getWarningMessages_spec__0(v_unreported_3967_, v___x_3966_, v___x_3965_);
lean_dec_ref(v_unreported_3967_);
v___x_3972_ = l_Lean_NameSet_empty;
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 2, v___x_3972_);
lean_ctor_set(v___x_3969_, 1, v___x_3971_);
lean_ctor_set(v___x_3969_, 0, v___x_3966_);
v___x_3974_ = v___x_3969_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3966_);
lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3971_);
lean_ctor_set(v_reuseFailAlloc_3975_, 2, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___redArg(lean_object* v_inst_3979_, lean_object* v_log_3980_, lean_object* v_f_3981_){
_start:
{
lean_object* v_unreported_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v_unreported_3982_ = lean_ctor_get(v_log_3980_, 1);
lean_inc_ref(v_unreported_3982_);
lean_dec_ref(v_log_3980_);
v___x_3983_ = lean_unsigned_to_nat(0u);
v___x_3984_ = l_Lean_PersistentArray_forM___redArg(v_inst_3979_, v_unreported_3982_, v_f_3981_, v___x_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM(lean_object* v_m_3985_, lean_object* v_inst_3986_, lean_object* v_log_3987_, lean_object* v_f_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_MessageLog_forM___redArg(v_inst_3986_, v_log_3987_, v_f_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList(lean_object* v_log_3990_){
_start:
{
lean_object* v_unreported_3991_; lean_object* v___x_3992_; 
v_unreported_3991_ = lean_ctor_get(v_log_3990_, 1);
v___x_3992_ = l_Lean_PersistentArray_toList___redArg(v_unreported_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toList___boxed(lean_object* v_log_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_MessageLog_toList(v_log_3993_);
lean_dec_ref(v_log_3993_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray(lean_object* v_log_3995_){
_start:
{
lean_object* v_unreported_3996_; lean_object* v___x_3997_; 
v_unreported_3996_ = lean_ctor_get(v_log_3995_, 1);
v___x_3997_ = l_Lean_PersistentArray_toArray___redArg(v_unreported_3996_);
return v___x_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_toArray___boxed(lean_object* v_log_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_MessageLog_toArray(v_log_3998_);
lean_dec_ref(v_log_3998_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_nestD(lean_object* v_msg_4000_){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_unsigned_to_nat(2u);
v___x_4002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v_msg_4000_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentD(lean_object* v_msg_4003_){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v_msg_4003_);
v___x_4006_ = l_Lean_MessageData_nestD(v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_indentExpr(lean_object* v_e_4007_){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = l_Lean_MessageData_ofExpr(v_e_4007_);
v___x_4009_ = l_Lean_indentD(v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively(lean_object* v_ctx_4010_, lean_object* v_msg_4011_){
_start:
{
lean_object* v_env_4013_; lean_object* v_mctx_4014_; lean_object* v_lctx_4015_; lean_object* v_opts_4016_; lean_object* v_currNamespace_4017_; lean_object* v_openDecls_4018_; lean_object* v___x_4019_; lean_object* v_msg_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_env_4013_ = lean_ctor_get(v_ctx_4010_, 0);
v_mctx_4014_ = lean_ctor_get(v_ctx_4010_, 1);
v_lctx_4015_ = lean_ctor_get(v_ctx_4010_, 2);
v_opts_4016_ = lean_ctor_get(v_ctx_4010_, 3);
v_currNamespace_4017_ = lean_ctor_get(v_ctx_4010_, 4);
v_openDecls_4018_ = lean_ctor_get(v_ctx_4010_, 5);
lean_inc(v_openDecls_4018_);
lean_inc(v_currNamespace_4017_);
v___x_4019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4019_, 0, v_currNamespace_4017_);
lean_ctor_set(v___x_4019_, 1, v_openDecls_4018_);
v_msg_4020_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_msg_4020_, 0, v___x_4019_);
lean_ctor_set(v_msg_4020_, 1, v_msg_4011_);
lean_inc_ref(v_opts_4016_);
lean_inc_ref(v_lctx_4015_);
lean_inc_ref(v_mctx_4014_);
lean_inc_ref(v_env_4013_);
v___x_4021_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4021_, 0, v_env_4013_);
lean_ctor_set(v___x_4021_, 1, v_mctx_4014_);
lean_ctor_set(v___x_4021_, 2, v_lctx_4015_);
lean_ctor_set(v___x_4021_, 3, v_opts_4016_);
v___x_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
v___x_4023_ = l_Lean_MessageData_format(v_msg_4020_, v___x_4022_);
v___x_4024_ = l_Std_Format_defWidth;
v___x_4025_ = lean_unsigned_to_nat(0u);
v___x_4026_ = l_Std_Format_pretty(v___x_4023_, v___x_4024_, v___x_4025_, v___x_4025_);
return v___x_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_MessageData_formatExpensively___boxed(lean_object* v_ctx_4027_, lean_object* v_msg_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4027_, v_msg_4028_);
lean_dec_ref(v_ctx_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(lean_object* v_s_4031_, lean_object* v_a_4032_, uint8_t v_b_4033_){
_start:
{
lean_object* v_str_4034_; lean_object* v_startInclusive_4035_; lean_object* v_endExclusive_4036_; lean_object* v___x_4037_; uint8_t v_decide_4038_; 
v_str_4034_ = lean_ctor_get(v_s_4031_, 0);
v_startInclusive_4035_ = lean_ctor_get(v_s_4031_, 1);
v_endExclusive_4036_ = lean_ctor_get(v_s_4031_, 2);
v___x_4037_ = lean_nat_sub(v_endExclusive_4036_, v_startInclusive_4035_);
v_decide_4038_ = lean_nat_dec_eq(v_a_4032_, v___x_4037_);
lean_dec(v___x_4037_);
if (v_decide_4038_ == 0)
{
lean_object* v___x_4039_; uint32_t v___x_4040_; uint32_t v___x_4041_; uint8_t v___x_4042_; 
v___x_4039_ = lean_nat_add(v_startInclusive_4035_, v_a_4032_);
lean_dec(v_a_4032_);
v___x_4040_ = lean_string_utf8_get_fast(v_str_4034_, v___x_4039_);
v___x_4041_ = 10;
v___x_4042_ = lean_uint32_dec_eq(v___x_4040_, v___x_4041_);
if (v___x_4042_ == 0)
{
lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4043_ = lean_string_utf8_next_fast(v_str_4034_, v___x_4039_);
lean_dec(v___x_4039_);
v___x_4044_ = lean_nat_sub(v___x_4043_, v_startInclusive_4035_);
v_a_4032_ = v___x_4044_;
v_b_4033_ = v___x_4042_;
goto _start;
}
else
{
lean_dec(v___x_4039_);
return v___x_4042_;
}
}
else
{
lean_dec(v_a_4032_);
return v_b_4033_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg___boxed(lean_object* v_s_4046_, lean_object* v_a_4047_, lean_object* v_b_4048_){
_start:
{
uint8_t v_b_boxed_4049_; uint8_t v_res_4050_; lean_object* v_r_4051_; 
v_b_boxed_4049_ = lean_unbox(v_b_4048_);
v_res_4050_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4046_, v_a_4047_, v_b_boxed_4049_);
lean_dec_ref(v_s_4046_);
v_r_4051_ = lean_box(v_res_4050_);
return v_r_4051_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(lean_object* v_s_4052_){
_start:
{
lean_object* v_searcher_4053_; uint8_t v___x_4054_; uint8_t v___x_4055_; 
v_searcher_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = 0;
v___x_4055_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4052_, v_searcher_4053_, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_inlineExpr_spec__1___boxed(lean_object* v_s_4056_){
_start:
{
uint8_t v_res_4057_; lean_object* v_r_4058_; 
v_res_4057_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v_s_4056_);
lean_dec_ref(v_s_4056_);
v_r_4058_ = lean_box(v_res_4057_);
return v_r_4058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(lean_object* v___x_4059_, lean_object* v_val_4060_, lean_object* v_a_4061_, lean_object* v_b_4062_){
_start:
{
uint8_t v_decide_4063_; 
v_decide_4063_ = lean_nat_dec_eq(v_a_4061_, v___x_4059_);
if (v_decide_4063_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4064_ = lean_string_utf8_next_fast(v_val_4060_, v_a_4061_);
lean_dec(v_a_4061_);
v___x_4065_ = lean_unsigned_to_nat(1u);
v___x_4066_ = lean_nat_add(v_b_4062_, v___x_4065_);
lean_dec(v_b_4062_);
v_a_4061_ = v___x_4064_;
v_b_4062_ = v___x_4066_;
goto _start;
}
else
{
lean_dec(v_a_4061_);
return v_b_4062_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg___boxed(lean_object* v___x_4068_, lean_object* v_val_4069_, lean_object* v_a_4070_, lean_object* v_b_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4068_, v_val_4069_, v_a_4070_, v_b_4071_);
lean_dec_ref(v_val_4069_);
lean_dec(v___x_4068_);
return v_res_4072_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_MessageData_formatAux___closed__2));
v___x_4074_ = l_Lean_MessageData_ofFormat(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__2));
v___x_4079_ = l_Lean_MessageData_ofFormat(v___x_4078_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_inlineExpr___lam__0___closed__6(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = ((lean_object*)(l_Lean_inlineExpr___lam__0___closed__5));
v___x_4084_ = l_Lean_MessageData_ofFormat(v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0(lean_object* v_e_4085_, lean_object* v_maxInlineLength_4086_, lean_object* v_ctx_4087_){
_start:
{
lean_object* v_msg_4089_; lean_object* v___x_4090_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_msg_4089_ = l_Lean_MessageData_ofExpr(v_e_4085_);
lean_inc_ref(v_msg_4089_);
v___x_4090_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4087_, v_msg_4089_);
v___x_4095_ = lean_unsigned_to_nat(0u);
v___x_4096_ = lean_string_utf8_byte_size(v___x_4090_);
lean_inc_ref(v___x_4090_);
v___x_4097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4090_);
lean_ctor_set(v___x_4097_, 1, v___x_4095_);
lean_ctor_set(v___x_4097_, 2, v___x_4096_);
v___x_4098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4096_, v___x_4090_, v___x_4095_, v___x_4095_);
lean_dec_ref(v___x_4090_);
v___x_4099_ = lean_nat_dec_lt(v_maxInlineLength_4086_, v___x_4098_);
lean_dec(v___x_4098_);
if (v___x_4099_ == 0)
{
uint8_t v___x_4100_; 
v___x_4100_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4097_);
lean_dec_ref_known(v___x_4097_, 3);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4101_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v_msg_4089_);
v___x_4103_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
return v___x_4104_;
}
else
{
goto v___jp_4091_;
}
}
else
{
lean_dec_ref_known(v___x_4097_, 3);
goto v___jp_4091_;
}
v___jp_4091_:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4092_ = l_Lean_indentD(v_msg_4089_);
v___x_4093_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__0, &l_Lean_inlineExpr___lam__0___closed__0_once, _init_l_Lean_inlineExpr___lam__0___closed__0);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
return v___x_4094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__0___boxed(lean_object* v_e_4105_, lean_object* v_maxInlineLength_4106_, lean_object* v_ctx_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_inlineExpr___lam__0(v_e_4105_, v_maxInlineLength_4106_, v_ctx_4107_);
lean_dec_ref(v_ctx_4107_);
lean_dec(v_maxInlineLength_4106_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2(lean_object* v_e_4110_, lean_object* v_x_4111_){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4113_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4114_ = l_Lean_MessageData_ofExpr(v_e_4110_);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4113_);
lean_ctor_set(v___x_4115_, 1, v___x_4114_);
v___x_4116_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__6, &l_Lean_inlineExpr___lam__0___closed__6_once, _init_l_Lean_inlineExpr___lam__0___closed__6);
v___x_4117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr___lam__2___boxed(lean_object* v_e_4118_, lean_object* v_x_4119_, lean_object* v___y_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Lean_inlineExpr___lam__2(v_e_4118_, v_x_4119_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExpr(lean_object* v_e_4122_, lean_object* v_maxInlineLength_4123_){
_start:
{
lean_object* v___f_4124_; lean_object* v___f_4125_; lean_object* v___f_4126_; lean_object* v___x_4127_; 
lean_inc_ref_n(v_e_4122_, 2);
v___f_4124_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4124_, 0, v_e_4122_);
lean_closure_set(v___f_4124_, 1, v_maxInlineLength_4123_);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4125_, 0, v_e_4122_);
v___f_4126_ = lean_alloc_closure((void*)(l_Lean_inlineExpr___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4126_, 0, v_e_4122_);
v___x_4127_ = l_Lean_MessageData_lazy(v___f_4124_, v___f_4125_, v___f_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(lean_object* v___x_4128_, lean_object* v___x_4129_, lean_object* v_val_4130_, lean_object* v_inst_4131_, lean_object* v_R_4132_, lean_object* v_a_4133_, lean_object* v_b_4134_, lean_object* v_c_4135_){
_start:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4128_, v_val_4130_, v_a_4133_, v_b_4134_);
return v___x_4136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___boxed(lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_val_4139_, lean_object* v_inst_4140_, lean_object* v_R_4141_, lean_object* v_a_4142_, lean_object* v_b_4143_, lean_object* v_c_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0(v___x_4137_, v___x_4138_, v_val_4139_, v_inst_4140_, v_R_4141_, v_a_4142_, v_b_4143_, v_c_4144_);
lean_dec_ref(v_val_4139_);
lean_dec_ref(v___x_4138_);
lean_dec(v___x_4137_);
return v_res_4145_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(lean_object* v_s_4146_, lean_object* v_inst_4147_, lean_object* v_R_4148_, lean_object* v_a_4149_, uint8_t v_b_4150_, lean_object* v_c_4151_){
_start:
{
uint8_t v___x_4152_; 
v___x_4152_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___redArg(v_s_4146_, v_a_4149_, v_b_4150_);
return v___x_4152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1___boxed(lean_object* v_s_4153_, lean_object* v_inst_4154_, lean_object* v_R_4155_, lean_object* v_a_4156_, lean_object* v_b_4157_, lean_object* v_c_4158_){
_start:
{
uint8_t v_b_boxed_4159_; uint8_t v_res_4160_; lean_object* v_r_4161_; 
v_b_boxed_4159_ = lean_unbox(v_b_4157_);
v_res_4160_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_inlineExpr_spec__1_spec__1(v_s_4153_, v_inst_4154_, v_R_4155_, v_a_4156_, v_b_boxed_4159_, v_c_4158_);
lean_dec_ref(v_s_4153_);
v_r_4161_ = lean_box(v_res_4160_);
return v_r_4161_;
}
}
static lean_object* _init_l_Lean_inlineExprTrailing___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = ((lean_object*)(l_Lean_inlineExprTrailing___lam__0___closed__1));
v___x_4166_ = l_Lean_MessageData_ofFormat(v___x_4165_);
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0(lean_object* v_e_4167_, lean_object* v_maxInlineLength_4168_, lean_object* v_ctx_4169_){
_start:
{
lean_object* v_msg_4171_; lean_object* v___x_4172_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; uint8_t v___x_4179_; 
v_msg_4171_ = l_Lean_MessageData_ofExpr(v_e_4167_);
lean_inc_ref(v_msg_4171_);
v___x_4172_ = l___private_Lean_Message_0__Lean_MessageData_formatExpensively(v_ctx_4169_, v_msg_4171_);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = lean_string_utf8_byte_size(v___x_4172_);
lean_inc_ref(v___x_4172_);
v___x_4177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4172_);
lean_ctor_set(v___x_4177_, 1, v___x_4175_);
lean_ctor_set(v___x_4177_, 2, v___x_4176_);
v___x_4178_ = l_WellFounded_opaqueFix_u2083___at___00Lean_inlineExpr_spec__0___redArg(v___x_4176_, v___x_4172_, v___x_4175_, v___x_4175_);
lean_dec_ref(v___x_4172_);
v___x_4179_ = lean_nat_dec_lt(v_maxInlineLength_4168_, v___x_4178_);
lean_dec(v___x_4178_);
if (v___x_4179_ == 0)
{
uint8_t v___x_4180_; 
v___x_4180_ = l_String_Slice_contains___at___00Lean_inlineExpr_spec__1(v___x_4177_);
lean_dec_ref_known(v___x_4177_, 3);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4181_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
lean_ctor_set(v___x_4182_, 1, v_msg_4171_);
v___x_4183_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4182_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
return v___x_4184_;
}
else
{
goto v___jp_4173_;
}
}
else
{
lean_dec_ref_known(v___x_4177_, 3);
goto v___jp_4173_;
}
v___jp_4173_:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Lean_indentD(v_msg_4171_);
return v___x_4174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__0___boxed(lean_object* v_e_4185_, lean_object* v_maxInlineLength_4186_, lean_object* v_ctx_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_inlineExprTrailing___lam__0(v_e_4185_, v_maxInlineLength_4186_, v_ctx_4187_);
lean_dec_ref(v_ctx_4187_);
lean_dec(v_maxInlineLength_4186_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2(lean_object* v_e_4190_, lean_object* v_x_4191_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4193_ = lean_obj_once(&l_Lean_inlineExpr___lam__0___closed__3, &l_Lean_inlineExpr___lam__0___closed__3_once, _init_l_Lean_inlineExpr___lam__0___closed__3);
v___x_4194_ = l_Lean_MessageData_ofExpr(v_e_4190_);
v___x_4195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_obj_once(&l_Lean_inlineExprTrailing___lam__0___closed__2, &l_Lean_inlineExprTrailing___lam__0___closed__2_once, _init_l_Lean_inlineExprTrailing___lam__0___closed__2);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing___lam__2___boxed(lean_object* v_e_4198_, lean_object* v_x_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_inlineExprTrailing___lam__2(v_e_4198_, v_x_4199_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_inlineExprTrailing(lean_object* v_e_4202_, lean_object* v_maxInlineLength_4203_){
_start:
{
lean_object* v___f_4204_; lean_object* v___f_4205_; lean_object* v___f_4206_; lean_object* v___x_4207_; 
lean_inc_ref_n(v_e_4202_, 2);
v___f_4204_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__0___boxed), 4, 2);
lean_closure_set(v___f_4204_, 0, v_e_4202_);
lean_closure_set(v___f_4204_, 1, v_maxInlineLength_4203_);
v___f_4205_ = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4205_, 0, v_e_4202_);
v___f_4206_ = lean_alloc_closure((void*)(l_Lean_inlineExprTrailing___lam__2___boxed), 3, 1);
lean_closure_set(v___f_4206_, 0, v_e_4202_);
v___x_4207_ = l_Lean_MessageData_lazy(v___f_4204_, v___f_4205_, v___f_4206_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_aquote___closed__2(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = ((lean_object*)(l_Lean_aquote___closed__1));
v___x_4212_ = l_Lean_MessageData_ofFormat(v___x_4211_);
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_aquote___closed__5(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = ((lean_object*)(l_Lean_aquote___closed__4));
v___x_4217_ = l_Lean_MessageData_ofFormat(v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_aquote(lean_object* v_msg_4218_){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4219_ = lean_obj_once(&l_Lean_aquote___closed__2, &l_Lean_aquote___closed__2_once, _init_l_Lean_aquote___closed__2);
v___x_4220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4219_);
lean_ctor_set(v___x_4220_, 1, v_msg_4218_);
v___x_4221_ = lean_obj_once(&l_Lean_aquote___closed__5, &l_Lean_aquote___closed__5_once, _init_l_Lean_aquote___closed__5);
v___x_4222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4220_);
lean_ctor_set(v___x_4222_, 1, v___x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object* v_inst_4223_, lean_object* v_inst_4224_, lean_object* v_msg_4225_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4226_ = lean_apply_1(v_inst_4223_, v_msg_4225_);
v___x_4227_ = lean_apply_2(v_inst_4224_, lean_box(0), v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg(lean_object* v_inst_4228_, lean_object* v_inst_4229_){
_start:
{
lean_object* v___f_4230_; 
v___f_4230_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4230_, 0, v_inst_4229_);
lean_closure_set(v___f_4230_, 1, v_inst_4228_);
return v___f_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddMessageContextOfMonadLift(lean_object* v_m_4231_, lean_object* v_n_4232_, lean_object* v_inst_4233_, lean_object* v_inst_4234_){
_start:
{
lean_object* v___f_4235_; 
v___f_4235_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4235_, 0, v_inst_4234_);
lean_closure_set(v___f_4235_, 1, v_inst_4233_);
return v___f_4235_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4236_ = lean_unsigned_to_nat(32u);
v___x_4237_ = lean_mk_empty_array_with_capacity(v___x_4236_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1(void){
_start:
{
size_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4239_ = ((size_t)5ULL);
v___x_4240_ = lean_unsigned_to_nat(0u);
v___x_4241_ = lean_unsigned_to_nat(32u);
v___x_4242_ = lean_mk_empty_array_with_capacity(v___x_4241_);
v___x_4243_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__0, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__0_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__0);
v___x_4244_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4244_, 0, v___x_4243_);
lean_ctor_set(v___x_4244_, 1, v___x_4242_);
lean_ctor_set(v___x_4244_, 2, v___x_4240_);
lean_ctor_set(v___x_4244_, 3, v___x_4240_);
lean_ctor_set_usize(v___x_4244_, 4, v___x_4239_);
return v___x_4244_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4245_ = lean_box(1);
v___x_4246_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4247_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__1);
v___x_4248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v___x_4246_);
lean_ctor_set(v___x_4248_, 2, v___x_4245_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__0(lean_object* v_env_4249_, lean_object* v_msgData_4250_, lean_object* v_toPure_4251_, lean_object* v_opts_4252_){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4253_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4254_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__2, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__2_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__2);
v___x_4255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4255_, 0, v_env_4249_);
lean_ctor_set(v___x_4255_, 1, v___x_4253_);
lean_ctor_set(v___x_4255_, 2, v___x_4254_);
lean_ctor_set(v___x_4255_, 3, v_opts_4252_);
v___x_4256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v_msgData_4250_);
v___x_4257_ = lean_apply_2(v_toPure_4251_, lean_box(0), v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg___lam__1(lean_object* v_inst_4258_, lean_object* v_msgData_4259_, lean_object* v_toPure_4260_, lean_object* v_toBind_4261_, lean_object* v_____do__lift_4262_){
_start:
{
lean_object* v_getOptionsUnrestricted_4263_; uint8_t v___x_4264_; lean_object* v_env_4265_; lean_object* v___f_4266_; lean_object* v___x_4267_; 
v_getOptionsUnrestricted_4263_ = lean_ctor_get(v_inst_4258_, 1);
lean_inc(v_getOptionsUnrestricted_4263_);
lean_dec_ref(v_inst_4258_);
v___x_4264_ = 0;
v_env_4265_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4262_, v___x_4264_);
v___f_4266_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__0), 4, 3);
lean_closure_set(v___f_4266_, 0, v_env_4265_);
lean_closure_set(v___f_4266_, 1, v_msgData_4259_);
lean_closure_set(v___f_4266_, 2, v_toPure_4260_);
v___x_4267_ = lean_apply_4(v_toBind_4261_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4263_, v___f_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___redArg(lean_object* v_inst_4268_, lean_object* v_inst_4269_, lean_object* v_inst_4270_, lean_object* v_msgData_4271_){
_start:
{
lean_object* v_toApplicative_4272_; lean_object* v_toBind_4273_; lean_object* v_getEnv_4274_; lean_object* v_toPure_4275_; lean_object* v___f_4276_; lean_object* v___x_4277_; 
v_toApplicative_4272_ = lean_ctor_get(v_inst_4268_, 0);
lean_inc_ref(v_toApplicative_4272_);
v_toBind_4273_ = lean_ctor_get(v_inst_4268_, 1);
lean_inc_n(v_toBind_4273_, 2);
lean_dec_ref(v_inst_4268_);
v_getEnv_4274_ = lean_ctor_get(v_inst_4269_, 0);
lean_inc(v_getEnv_4274_);
lean_dec_ref(v_inst_4269_);
v_toPure_4275_ = lean_ctor_get(v_toApplicative_4272_, 1);
lean_inc(v_toPure_4275_);
lean_dec_ref(v_toApplicative_4272_);
v___f_4276_ = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___redArg___lam__1), 5, 4);
lean_closure_set(v___f_4276_, 0, v_inst_4270_);
lean_closure_set(v___f_4276_, 1, v_msgData_4271_);
lean_closure_set(v___f_4276_, 2, v_toPure_4275_);
lean_closure_set(v___f_4276_, 3, v_toBind_4273_);
v___x_4277_ = lean_apply_4(v_toBind_4273_, lean_box(0), lean_box(0), v_getEnv_4274_, v___f_4276_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial(lean_object* v_m_4278_, lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_msgData_4282_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_addMessageContextPartial___redArg(v_inst_4279_, v_inst_4280_, v_inst_4281_, v_msgData_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__0(lean_object* v_env_4284_, lean_object* v_mctx_4285_, lean_object* v_lctx_4286_, lean_object* v_msgData_4287_, lean_object* v_toPure_4288_, lean_object* v_opts_4289_){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4290_, 0, v_env_4284_);
lean_ctor_set(v___x_4290_, 1, v_mctx_4285_);
lean_ctor_set(v___x_4290_, 2, v_lctx_4286_);
lean_ctor_set(v___x_4290_, 3, v_opts_4289_);
v___x_4291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v_msgData_4287_);
v___x_4292_ = lean_apply_2(v_toPure_4288_, lean_box(0), v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__1(lean_object* v_inst_4293_, lean_object* v_env_4294_, lean_object* v_mctx_4295_, lean_object* v_msgData_4296_, lean_object* v_toPure_4297_, lean_object* v_toBind_4298_, lean_object* v_lctx_4299_){
_start:
{
lean_object* v_getOptionsUnrestricted_4300_; lean_object* v___f_4301_; lean_object* v___x_4302_; 
v_getOptionsUnrestricted_4300_ = lean_ctor_get(v_inst_4293_, 1);
lean_inc(v_getOptionsUnrestricted_4300_);
lean_dec_ref(v_inst_4293_);
v___f_4301_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__0), 6, 5);
lean_closure_set(v___f_4301_, 0, v_env_4294_);
lean_closure_set(v___f_4301_, 1, v_mctx_4295_);
lean_closure_set(v___f_4301_, 2, v_lctx_4299_);
lean_closure_set(v___f_4301_, 3, v_msgData_4296_);
lean_closure_set(v___f_4301_, 4, v_toPure_4297_);
v___x_4302_ = lean_apply_4(v_toBind_4298_, lean_box(0), lean_box(0), v_getOptionsUnrestricted_4300_, v___f_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__2(lean_object* v_inst_4303_, lean_object* v_env_4304_, lean_object* v_msgData_4305_, lean_object* v_toPure_4306_, lean_object* v_toBind_4307_, lean_object* v_inst_4308_, lean_object* v_mctx_4309_){
_start:
{
lean_object* v___f_4310_; lean_object* v___x_4311_; 
lean_inc(v_toBind_4307_);
v___f_4310_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__1), 7, 6);
lean_closure_set(v___f_4310_, 0, v_inst_4303_);
lean_closure_set(v___f_4310_, 1, v_env_4304_);
lean_closure_set(v___f_4310_, 2, v_mctx_4309_);
lean_closure_set(v___f_4310_, 3, v_msgData_4305_);
lean_closure_set(v___f_4310_, 4, v_toPure_4306_);
lean_closure_set(v___f_4310_, 5, v_toBind_4307_);
v___x_4311_ = lean_apply_4(v_toBind_4307_, lean_box(0), lean_box(0), v_inst_4308_, v___f_4310_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___redArg___lam__3(lean_object* v_inst_4312_, lean_object* v_inst_4313_, lean_object* v_msgData_4314_, lean_object* v_toPure_4315_, lean_object* v_toBind_4316_, lean_object* v_inst_4317_, lean_object* v_____do__lift_4318_){
_start:
{
lean_object* v_getMCtx_4319_; uint8_t v___x_4320_; lean_object* v_env_4321_; lean_object* v___f_4322_; lean_object* v___x_4323_; 
v_getMCtx_4319_ = lean_ctor_get(v_inst_4312_, 0);
lean_inc(v_getMCtx_4319_);
lean_dec_ref(v_inst_4312_);
v___x_4320_ = 0;
v_env_4321_ = l_Lean_Environment_setRecordingDeps(v_____do__lift_4318_, v___x_4320_);
lean_inc(v_toBind_4316_);
v___f_4322_ = lean_alloc_closure((void*)(l_Lean_addMessageContextFull___redArg___lam__2), 7, 6);
lean_closure_set(v___f_4322_, 0, v_inst_4313_);
lean_closure_set(v___f_4322_, 1, v_env_4321_);
lean_closure_set(v___f_4322_, 2, v_msgData_4314_);
lean_closure_set(v___f_4322_, 3, v_toPure_4315_);
lean_closure_set(v___f_4322_, 4, v_toBind_4316_);
lean_closure_set(v___f_4322_, 5, v_inst_4317_);
v___x_4323_ = lean_apply_4(v_toBind_4316_, lean_box(0), lean_box(0), v_getMCtx_4319_, v___f_4322_);
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
lean_closure_set(v___f_4334_, 1, v_inst_4328_);
lean_closure_set(v___f_4334_, 2, v_msgData_4329_);
lean_closure_set(v___f_4334_, 3, v_toPure_4333_);
lean_closure_set(v___f_4334_, 4, v_toBind_4331_);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg(){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___closed__0));
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg___boxed(lean_object* v___dummy_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v_res_4349_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___redArg();
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(lean_object* v_s_4351_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___boxed(lean_object* v_s_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0(v_s_4353_);
lean_dec_ref(v_s_4353_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(lean_object* v_str_4355_, lean_object* v___x_4356_, lean_object* v___x_4357_, lean_object* v_a_4358_, lean_object* v_b_4359_){
_start:
{
lean_object* v_it_4361_; lean_object* v_startInclusive_4362_; lean_object* v_endExclusive_4363_; 
if (lean_obj_tag(v_a_4358_) == 0)
{
lean_object* v_currPos_4369_; lean_object* v_searcher_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4393_; 
v_currPos_4369_ = lean_ctor_get(v_a_4358_, 0);
v_searcher_4370_ = lean_ctor_get(v_a_4358_, 1);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_a_4358_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4372_ = v_a_4358_;
v_isShared_4373_ = v_isSharedCheck_4393_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_searcher_4370_);
lean_inc(v_currPos_4369_);
lean_dec(v_a_4358_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4393_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
uint8_t v_decide_4374_; 
v_decide_4374_ = lean_nat_dec_eq(v_searcher_4370_, v___x_4357_);
if (v_decide_4374_ == 0)
{
uint32_t v___x_4375_; uint32_t v___x_4376_; uint8_t v___x_4377_; 
v___x_4375_ = 10;
v___x_4376_ = lean_string_utf8_get_fast(v_str_4355_, v_searcher_4370_);
v___x_4377_ = lean_uint32_dec_eq(v___x_4376_, v___x_4375_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; lean_object* v___x_4380_; 
v___x_4378_ = lean_string_utf8_next_fast(v_str_4355_, v_searcher_4370_);
lean_dec(v_searcher_4370_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 1, v___x_4378_);
v___x_4380_ = v___x_4372_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_currPos_4369_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___x_4378_);
v___x_4380_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
v_a_4358_ = v___x_4380_;
goto _start;
}
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v_slice_4386_; lean_object* v_nextIt_4388_; 
v___x_4383_ = lean_string_utf8_next_fast(v_str_4355_, v_searcher_4370_);
v___x_4384_ = lean_nat_sub(v___x_4383_, v_searcher_4370_);
v___x_4385_ = lean_nat_add(v_searcher_4370_, v___x_4384_);
lean_dec(v___x_4384_);
v_slice_4386_ = l_String_Slice_subslice_x21(v___x_4356_, v_currPos_4369_, v_searcher_4370_);
lean_inc(v___x_4385_);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 1, v___x_4385_);
lean_ctor_set(v___x_4372_, 0, v___x_4385_);
v_nextIt_4388_ = v___x_4372_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4385_);
lean_ctor_set(v_reuseFailAlloc_4391_, 1, v___x_4385_);
v_nextIt_4388_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v_startInclusive_4389_; lean_object* v_endExclusive_4390_; 
v_startInclusive_4389_ = lean_ctor_get(v_slice_4386_, 0);
lean_inc(v_startInclusive_4389_);
v_endExclusive_4390_ = lean_ctor_get(v_slice_4386_, 1);
lean_inc(v_endExclusive_4390_);
lean_dec_ref(v_slice_4386_);
v_it_4361_ = v_nextIt_4388_;
v_startInclusive_4362_ = v_startInclusive_4389_;
v_endExclusive_4363_ = v_endExclusive_4390_;
goto v___jp_4360_;
}
}
}
else
{
lean_object* v___x_4392_; 
lean_del_object(v___x_4372_);
lean_dec(v_searcher_4370_);
v___x_4392_ = lean_box(1);
lean_inc(v___x_4357_);
v_it_4361_ = v___x_4392_;
v_startInclusive_4362_ = v_currPos_4369_;
v_endExclusive_4363_ = v___x_4357_;
goto v___jp_4360_;
}
}
}
else
{
lean_dec(v___x_4357_);
return v_b_4359_;
}
v___jp_4360_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_string_utf8_extract_fast(v_str_4355_, v_startInclusive_4362_, v_endExclusive_4363_);
lean_dec(v_endExclusive_4363_);
lean_dec(v_startInclusive_4362_);
v___x_4365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
v___x_4366_ = l_Lean_MessageData_ofFormat(v___x_4365_);
v___x_4367_ = lean_array_push(v_b_4359_, v___x_4366_);
v_a_4358_ = v_it_4361_;
v_b_4359_ = v___x_4367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg___boxed(lean_object* v_str_4394_, lean_object* v___x_4395_, lean_object* v___x_4396_, lean_object* v_a_4397_, lean_object* v_b_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4394_, v___x_4395_, v___x_4396_, v_a_4397_, v_b_4398_);
lean_dec_ref(v___x_4395_);
lean_dec_ref(v_str_4394_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_stringToMessageData(lean_object* v_str_4402_){
_start:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v_lines_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4403_ = lean_unsigned_to_nat(0u);
v___x_4404_ = lean_string_utf8_byte_size(v_str_4402_);
lean_inc_ref(v_str_4402_);
v___x_4405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4405_, 0, v_str_4402_);
lean_ctor_set(v___x_4405_, 1, v___x_4403_);
lean_ctor_set(v___x_4405_, 2, v___x_4404_);
v_lines_4406_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_stringToMessageData_spec__0___closed__0);
v___x_4407_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4408_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4402_, v___x_4405_, v___x_4404_, v_lines_4406_, v___x_4407_);
lean_dec_ref_known(v___x_4405_, 3);
lean_dec_ref(v_str_4402_);
v___x_4409_ = lean_array_to_list(v___x_4408_);
v___x_4410_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4411_ = l_Lean_MessageData_joinSep(v___x_4409_, v___x_4410_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(lean_object* v_str_4412_, lean_object* v___x_4413_, lean_object* v___x_4414_, lean_object* v_inst_4415_, lean_object* v_R_4416_, lean_object* v_a_4417_, lean_object* v_b_4418_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___redArg(v_str_4412_, v___x_4413_, v___x_4414_, v_a_4417_, v_b_4418_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1___boxed(lean_object* v_str_4420_, lean_object* v___x_4421_, lean_object* v___x_4422_, lean_object* v_inst_4423_, lean_object* v_R_4424_, lean_object* v_a_4425_, lean_object* v_b_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_stringToMessageData_spec__1(v_str_4420_, v___x_4421_, v___x_4422_, v_inst_4423_, v_R_4424_, v_a_4425_, v_b_4426_);
lean_dec_ref(v___x_4421_);
lean_dec_ref(v_str_4420_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat___redArg(lean_object* v_inst_4428_){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = ((lean_object*)(l_Lean_MessageData_instCoeString___closed__1));
v___x_4430_ = lean_alloc_closure((void*)(l_Function_comp), 6, 5);
lean_closure_set(v___x_4430_, 0, lean_box(0));
lean_closure_set(v___x_4430_, 1, lean_box(0));
lean_closure_set(v___x_4430_, 2, lean_box(0));
lean_closure_set(v___x_4430_, 3, v___x_4429_);
lean_closure_set(v___x_4430_, 4, v_inst_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOfToFormat(lean_object* v_00_u03b1_4431_, lean_object* v_inst_4432_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_instToMessageDataOfToFormat___redArg(v_inst_4432_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg(){
_start:
{
lean_object* v___f_4441_; 
v___f_4441_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___redArg___boxed(lean_object* v___dummy_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_instToMessageDataTSyntax___redArg();
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax(lean_object* v_k_4444_){
_start:
{
lean_object* v___f_4445_; 
v___f_4445_ = ((lean_object*)(l_Lean_MessageData_instCoeSyntax___closed__0));
return v___f_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataTSyntax___boxed(lean_object* v_k_4446_){
_start:
{
lean_object* v_res_4447_; 
v_res_4447_ = l_Lean_instToMessageDataTSyntax(v_k_4446_);
lean_dec(v_k_4446_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg___lam__0(lean_object* v_inst_4452_, lean_object* v_as_4453_){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v___x_4454_ = lean_box(0);
v___x_4455_ = l_List_mapTR_loop___redArg(v_inst_4452_, v_as_4453_, v___x_4454_);
v___x_4456_ = l_Lean_MessageData_ofList(v___x_4455_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList___redArg(lean_object* v_inst_4457_){
_start:
{
lean_object* v___f_4458_; 
v___f_4458_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4458_, 0, v_inst_4457_);
return v___f_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataList(lean_object* v_00_u03b1_4459_, lean_object* v_inst_4460_){
_start:
{
lean_object* v___f_4461_; 
v___f_4461_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataList___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4461_, 0, v_inst_4460_);
return v___f_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg___lam__0(lean_object* v_inst_4462_, lean_object* v_as_4463_){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v___x_4464_ = lean_array_to_list(v_as_4463_);
v___x_4465_ = lean_box(0);
v___x_4466_ = l_List_mapTR_loop___redArg(v_inst_4462_, v___x_4464_, v___x_4465_);
v___x_4467_ = l_Lean_MessageData_ofList(v___x_4466_);
return v___x_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray___redArg(lean_object* v_inst_4468_){
_start:
{
lean_object* v___f_4469_; 
v___f_4469_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4469_, 0, v_inst_4468_);
return v___f_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataArray(lean_object* v_00_u03b1_4470_, lean_object* v_inst_4471_){
_start:
{
lean_object* v___f_4472_; 
v___f_4472_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataArray___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4472_, 0, v_inst_4471_);
return v___f_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__0(lean_object* v_it_4473_, lean_object* v_acc_4474_, lean_object* v_recur_4475_){
_start:
{
lean_object* v_array_4476_; lean_object* v_start_4477_; lean_object* v_stop_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4491_; 
v_array_4476_ = lean_ctor_get(v_it_4473_, 0);
v_start_4477_ = lean_ctor_get(v_it_4473_, 1);
v_stop_4478_ = lean_ctor_get(v_it_4473_, 2);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_it_4473_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4480_ = v_it_4473_;
v_isShared_4481_ = v_isSharedCheck_4491_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_stop_4478_);
lean_inc(v_start_4477_);
lean_inc(v_array_4476_);
lean_dec(v_it_4473_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4491_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
uint8_t v___x_4482_; 
v___x_4482_ = lean_nat_dec_lt(v_start_4477_, v_stop_4478_);
if (v___x_4482_ == 0)
{
lean_del_object(v___x_4480_);
lean_dec(v_stop_4478_);
lean_dec(v_start_4477_);
lean_dec_ref(v_array_4476_);
lean_dec_ref(v_recur_4475_);
return v_acc_4474_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4483_ = lean_unsigned_to_nat(1u);
v___x_4484_ = lean_nat_add(v_start_4477_, v___x_4483_);
lean_inc_ref(v_array_4476_);
if (v_isShared_4481_ == 0)
{
lean_ctor_set(v___x_4480_, 1, v___x_4484_);
v___x_4486_ = v___x_4480_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_array_4476_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v___x_4484_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_stop_4478_);
v___x_4486_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4487_ = lean_array_fget(v_array_4476_, v_start_4477_);
lean_dec(v_start_4477_);
lean_dec_ref(v_array_4476_);
v___x_4488_ = lean_array_push(v_acc_4474_, v___x_4487_);
v___x_4489_ = lean_apply_3(v_recur_4475_, v___x_4486_, v___x_4488_, lean_box(0));
return v___x_4489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg___lam__1(lean_object* v___f_4494_, lean_object* v_inst_4495_, lean_object* v_as_4496_){
_start:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4497_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___lam__1___closed__0));
v___x_4498_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_4494_, v_as_4496_, v___x_4497_);
v___x_4499_ = lean_array_to_list(v___x_4498_);
v___x_4500_ = lean_box(0);
v___x_4501_ = l_List_mapTR_loop___redArg(v_inst_4495_, v___x_4499_, v___x_4500_);
v___x_4502_ = l_Lean_MessageData_ofList(v___x_4501_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray___redArg(lean_object* v_inst_4504_){
_start:
{
lean_object* v___f_4505_; lean_object* v___f_4506_; 
v___f_4505_ = ((lean_object*)(l_Lean_instToMessageDataSubarray___redArg___closed__0));
v___f_4506_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataSubarray___redArg___lam__1), 3, 2);
lean_closure_set(v___f_4506_, 0, v___f_4505_);
lean_closure_set(v___f_4506_, 1, v_inst_4504_);
return v___f_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataSubarray(lean_object* v_00_u03b1_4507_, lean_object* v_inst_4508_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l_Lean_instToMessageDataSubarray___redArg(v_inst_4508_);
return v___x_4509_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__1));
v___x_4514_ = l_Lean_MessageData_ofFormat(v___x_4513_);
return v___x_4514_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = ((lean_object*)(l_Lean_instToMessageDataOption___redArg___lam__0___closed__3));
v___x_4518_ = l_Lean_MessageData_ofFormat(v___x_4517_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg___lam__0(lean_object* v_inst_4519_, lean_object* v_x_4520_){
_start:
{
if (lean_obj_tag(v_x_4520_) == 0)
{
lean_object* v___x_4521_; 
lean_dec_ref(v_inst_4519_);
v___x_4521_ = lean_obj_once(&l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2, &l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2_once, _init_l_Lean_MessageData_instCoeOptionExpr___lam__0___closed__2);
return v___x_4521_;
}
else
{
lean_object* v_val_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v_val_4522_ = lean_ctor_get(v_x_4520_, 0);
lean_inc(v_val_4522_);
lean_dec_ref_known(v_x_4520_, 1);
v___x_4523_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__2, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__2);
v___x_4524_ = lean_apply_1(v_inst_4519_, v_val_4522_);
v___x_4525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4523_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = lean_obj_once(&l_Lean_instToMessageDataOption___redArg___lam__0___closed__4, &l_Lean_instToMessageDataOption___redArg___lam__0___closed__4_once, _init_l_Lean_instToMessageDataOption___redArg___lam__0___closed__4);
v___x_4527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4525_);
lean_ctor_set(v___x_4527_, 1, v___x_4526_);
return v___x_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption___redArg(lean_object* v_inst_4528_){
_start:
{
lean_object* v___f_4529_; 
v___f_4529_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4529_, 0, v_inst_4528_);
return v___f_4529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOption(lean_object* v_00_u03b1_4530_, lean_object* v_inst_4531_){
_start:
{
lean_object* v___f_4532_; 
v___f_4532_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4532_, 0, v_inst_4531_);
return v___f_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg___lam__0(lean_object* v_inst_4533_, lean_object* v_inst_4534_, lean_object* v_x_4535_){
_start:
{
lean_object* v_fst_4536_; lean_object* v_snd_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4551_; 
v_fst_4536_ = lean_ctor_get(v_x_4535_, 0);
v_snd_4537_ = lean_ctor_get(v_x_4535_, 1);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_x_4535_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4539_ = v_x_4535_;
v_isShared_4540_ = v_isSharedCheck_4551_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_snd_4537_);
lean_inc(v_fst_4536_);
lean_dec(v_x_4535_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4551_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4544_; 
v___x_4541_ = lean_apply_1(v_inst_4533_, v_fst_4536_);
v___x_4542_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__5, &l_Lean_MessageData_ofList___closed__5_once, _init_l_Lean_MessageData_ofList___closed__5);
if (v_isShared_4540_ == 0)
{
lean_ctor_set_tag(v___x_4539_, 7);
lean_ctor_set(v___x_4539_, 1, v___x_4542_);
lean_ctor_set(v___x_4539_, 0, v___x_4541_);
v___x_4544_ = v___x_4539_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4541_);
lean_ctor_set(v_reuseFailAlloc_4550_, 1, v___x_4542_);
v___x_4544_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4545_ = lean_obj_once(&l_Lean_MessageData_ofList___closed__6, &l_Lean_MessageData_ofList___closed__6_once, _init_l_Lean_MessageData_ofList___closed__6);
v___x_4546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4546_, 0, v___x_4544_);
lean_ctor_set(v___x_4546_, 1, v___x_4545_);
v___x_4547_ = lean_apply_1(v_inst_4534_, v_snd_4537_);
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
v___x_4549_ = l_Lean_MessageData_paren(v___x_4548_);
return v___x_4549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd___redArg(lean_object* v_inst_4552_, lean_object* v_inst_4553_){
_start:
{
lean_object* v___f_4554_; 
v___f_4554_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4554_, 0, v_inst_4552_);
lean_closure_set(v___f_4554_, 1, v_inst_4553_);
return v___f_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataProd(lean_object* v_00_u03b1_4555_, lean_object* v_00_u03b2_4556_, lean_object* v_inst_4557_, lean_object* v_inst_4558_){
_start:
{
lean_object* v___f_4559_; 
v___f_4559_ = lean_alloc_closure((void*)(l_Lean_instToMessageDataProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_4559_, 0, v_inst_4557_);
lean_closure_set(v___f_4559_, 1, v_inst_4558_);
return v___f_4559_;
}
}
static lean_object* _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = ((lean_object*)(l_Lean_instToMessageDataOptionExpr___lam__0___closed__1));
v___x_4564_ = l_Lean_MessageData_ofFormat(v___x_4563_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToMessageDataOptionExpr___lam__0(lean_object* v_x_4565_){
_start:
{
if (lean_obj_tag(v_x_4565_) == 0)
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_obj_once(&l_Lean_instToMessageDataOptionExpr___lam__0___closed__2, &l_Lean_instToMessageDataOptionExpr___lam__0___closed__2_once, _init_l_Lean_instToMessageDataOptionExpr___lam__0___closed__2);
return v___x_4566_;
}
else
{
lean_object* v_val_4567_; lean_object* v___x_4568_; 
v_val_4567_ = lean_ctor_get(v_x_4565_, 0);
lean_inc(v_val_4567_);
lean_dec_ref_known(v_x_4565_, 1);
v___x_4568_ = l_Lean_MessageData_ofExpr(v_val_4567_);
return v___x_4568_;
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = ((lean_object*)(l_Lean_instImpl___closed__1_00___x40_Lean_Message_4238524789____hygCtx___hyg_139_));
v___x_4603_ = l_String_toRawSubstring_x27(v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__6));
v___x_4619_ = l_String_toRawSubstring_x27(v___x_4618_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(lean_object* v_x_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v___x_4636_; uint8_t v___x_4637_; 
v___x_4636_ = ((lean_object*)(l_Lean_termM_x21___00__closed__1));
lean_inc(v_x_4633_);
v___x_4637_ = l_Lean_Syntax_isOfKind(v_x_4633_, v___x_4636_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
lean_dec(v_x_4633_);
v___x_4638_ = lean_box(1);
v___x_4639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4638_);
lean_ctor_set(v___x_4639_, 1, v_a_4635_);
return v___x_4639_;
}
else
{
lean_object* v_quotContext_4640_; lean_object* v_currMacroScope_4641_; lean_object* v_ref_4642_; lean_object* v___x_4643_; lean_object* v_interpStr_4644_; uint8_t v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v_quotContext_4640_ = lean_ctor_get(v_a_4634_, 1);
v_currMacroScope_4641_ = lean_ctor_get(v_a_4634_, 2);
v_ref_4642_ = lean_ctor_get(v_a_4634_, 5);
v___x_4643_ = lean_unsigned_to_nat(1u);
v_interpStr_4644_ = l_Lean_Syntax_getArg(v_x_4633_, v___x_4643_);
lean_dec(v_x_4633_);
v___x_4645_ = 0;
v___x_4646_ = l_Lean_SourceInfo_fromRef(v_ref_4642_, v___x_4645_);
v___x_4647_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__0);
v___x_4648_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__1));
lean_inc_n(v_currMacroScope_4641_, 2);
lean_inc_n(v_quotContext_4640_, 2);
v___x_4649_ = l_Lean_addMacroScope(v_quotContext_4640_, v___x_4648_, v_currMacroScope_4641_);
v___x_4650_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__5));
lean_inc(v___x_4646_);
v___x_4651_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4646_);
lean_ctor_set(v___x_4651_, 1, v___x_4647_);
lean_ctor_set(v___x_4651_, 2, v___x_4649_);
lean_ctor_set(v___x_4651_, 3, v___x_4650_);
v___x_4652_ = lean_obj_once(&l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7, &l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7_once, _init_l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__7);
v___x_4653_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__8));
v___x_4654_ = l_Lean_addMacroScope(v_quotContext_4640_, v___x_4653_, v_currMacroScope_4641_);
v___x_4655_ = ((lean_object*)(l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___closed__12));
v___x_4656_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4646_);
lean_ctor_set(v___x_4656_, 1, v___x_4652_);
lean_ctor_set(v___x_4656_, 2, v___x_4654_);
lean_ctor_set(v___x_4656_, 3, v___x_4655_);
lean_inc_ref(v___x_4656_);
v___x_4657_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_4644_, v___x_4651_, v___x_4656_, v___x_4656_, v_a_4634_, v_a_4635_);
lean_dec(v_interpStr_4644_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4666_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_a_4659_ = lean_ctor_get(v___x_4657_, 1);
v_isSharedCheck_4666_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4666_ == 0)
{
v___x_4661_ = v___x_4657_;
v_isShared_4662_ = v_isSharedCheck_4666_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
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
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_4667_; lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4675_; 
v_a_4667_ = lean_ctor_get(v___x_4657_, 0);
v_a_4668_ = lean_ctor_get(v___x_4657_, 1);
v_isSharedCheck_4675_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4675_ == 0)
{
v___x_4670_ = v___x_4657_;
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_inc(v_a_4667_);
lean_dec(v___x_4657_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4675_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4673_; 
if (v_isShared_4671_ == 0)
{
v___x_4673_ = v___x_4670_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4667_);
lean_ctor_set(v_reuseFailAlloc_4674_, 1, v_a_4668_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1___boxed(lean_object* v_x_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean___aux__Lean__Message______macroRules__Lean__termM_x21____1(v_x_4676_, v_a_4677_, v_a_4678_);
lean_dec_ref(v_a_4677_);
return v_res_4679_;
}
}
static lean_object* _init_l_Lean_toMessageList___closed__1(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean_toMessageList___closed__0));
v___x_4682_ = l_Lean_stringToMessageData(v___x_4681_);
return v___x_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_toMessageList(lean_object* v_msgs_4683_){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4684_ = lean_array_to_list(v_msgs_4683_);
v___x_4685_ = lean_obj_once(&l_Lean_toMessageList___closed__1, &l_Lean_toMessageList___closed__1_once, _init_l_Lean_toMessageList___closed__1);
v___x_4686_ = l_Lean_MessageData_joinSep(v___x_4684_, v___x_4685_);
v___x_4687_ = l_Lean_indentD(v___x_4686_);
return v___x_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(lean_object* v_env_4688_, lean_object* v_lctx_4689_, lean_object* v_opts_4690_, lean_object* v_msg_4691_){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; 
v___x_4692_ = l_Lean_Environment_ofKernelEnv(v_env_4688_);
v___x_4693_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__2);
v___x_4694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4692_);
lean_ctor_set(v___x_4694_, 1, v___x_4693_);
lean_ctor_set(v___x_4694_, 2, v_lctx_4689_);
lean_ctor_set(v___x_4694_, 3, v_opts_4690_);
v___x_4695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
lean_ctor_set(v___x_4695_, 1, v_msg_4691_);
return v___x_4695_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__0));
v___x_4698_ = l_Lean_stringToMessageData(v___x_4697_);
return v___x_4698_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__2));
v___x_4701_ = l_Lean_stringToMessageData(v___x_4700_);
return v___x_4701_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___lam__0___closed__4));
v___x_4704_ = l_Lean_stringToMessageData(v___x_4703_);
return v___x_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData___lam__0(lean_object* v_givenType_4705_, lean_object* v_n_4706_, lean_object* v_expectedType_4707_){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4708_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__1);
v___x_4709_ = l_Lean_MessageData_ofName(v_n_4706_);
v___x_4710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4710_, 0, v___x_4708_);
lean_ctor_set(v___x_4710_, 1, v___x_4709_);
v___x_4711_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__3);
v___x_4712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4710_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = l_Lean_indentExpr(v_givenType_4705_);
v___x_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5, &l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___lam__0___closed__5);
v___x_4716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4714_);
lean_ctor_set(v___x_4716_, 1, v___x_4715_);
v___x_4717_ = l_Lean_indentExpr(v_expectedType_4707_);
v___x_4718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4716_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
return v___x_4718_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__0(void){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_obj_once(&l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0, &l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0_once, _init_l___private_Lean_Message_0__Lean_MessageData_hasSyntheticSorry_visit___closed__0);
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
return v___x_4720_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__1(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; 
v___x_4721_ = lean_box(1);
v___x_4722_ = lean_obj_once(&l_Lean_addMessageContextPartial___redArg___lam__0___closed__1, &l_Lean_addMessageContextPartial___redArg___lam__0___closed__1_once, _init_l_Lean_addMessageContextPartial___redArg___lam__0___closed__1);
v___x_4723_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__0, &l_Lean_Kernel_Exception_toMessageData___closed__0_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__0);
v___x_4724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4723_);
lean_ctor_set(v___x_4724_, 1, v___x_4722_);
lean_ctor_set(v___x_4724_, 2, v___x_4721_);
return v___x_4724_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__3(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__2));
v___x_4727_ = l_Lean_stringToMessageData(v___x_4726_);
return v___x_4727_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__5(void){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__4));
v___x_4730_ = l_Lean_stringToMessageData(v___x_4729_);
return v___x_4730_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__7(void){
_start:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__6));
v___x_4733_ = l_Lean_stringToMessageData(v___x_4732_);
return v___x_4733_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__10(void){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__9));
v___x_4738_ = l_Lean_MessageData_ofFormat(v___x_4737_);
return v___x_4738_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__12(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4740_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__11));
v___x_4741_ = l_Lean_stringToMessageData(v___x_4740_);
return v___x_4741_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__14(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__13));
v___x_4744_ = l_Lean_stringToMessageData(v___x_4743_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__16(void){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__15));
v___x_4747_ = l_Lean_stringToMessageData(v___x_4746_);
return v___x_4747_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__18(void){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__17));
v___x_4750_ = l_Lean_stringToMessageData(v___x_4749_);
return v___x_4750_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__20(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__19));
v___x_4753_ = l_Lean_stringToMessageData(v___x_4752_);
return v___x_4753_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__22(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__21));
v___x_4756_ = l_Lean_stringToMessageData(v___x_4755_);
return v___x_4756_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__24(void){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4758_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__23));
v___x_4759_ = l_Lean_stringToMessageData(v___x_4758_);
return v___x_4759_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__26(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__25));
v___x_4762_ = l_Lean_stringToMessageData(v___x_4761_);
return v___x_4762_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__28(void){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__27));
v___x_4765_ = l_Lean_stringToMessageData(v___x_4764_);
return v___x_4765_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__30(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__29));
v___x_4768_ = l_Lean_stringToMessageData(v___x_4767_);
return v___x_4768_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__32(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4770_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__31));
v___x_4771_ = l_Lean_stringToMessageData(v___x_4770_);
return v___x_4771_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__34(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__33));
v___x_4774_ = l_Lean_stringToMessageData(v___x_4773_);
return v___x_4774_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__36(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__35));
v___x_4777_ = l_Lean_stringToMessageData(v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__38(void){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4779_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__37));
v___x_4780_ = l_Lean_stringToMessageData(v___x_4779_);
return v___x_4780_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__41(void){
_start:
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__40));
v___x_4785_ = l_Lean_MessageData_ofFormat(v___x_4784_);
return v___x_4785_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__44(void){
_start:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
v___x_4789_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__43));
v___x_4790_ = l_Lean_MessageData_ofFormat(v___x_4789_);
return v___x_4790_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__47(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__46));
v___x_4795_ = l_Lean_MessageData_ofFormat(v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Kernel_Exception_toMessageData___closed__50(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = ((lean_object*)(l_Lean_Kernel_Exception_toMessageData___closed__49));
v___x_4800_ = l_Lean_MessageData_ofFormat(v___x_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object* v_e_4801_, lean_object* v_opts_4802_){
_start:
{
switch(lean_obj_tag(v_e_4801_))
{
case 0:
{
lean_object* v_env_4803_; lean_object* v_name_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4817_; 
v_env_4803_ = lean_ctor_get(v_e_4801_, 0);
v_name_4804_ = lean_ctor_get(v_e_4801_, 1);
v_isSharedCheck_4817_ = !lean_is_exclusive(v_e_4801_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4806_ = v_e_4801_;
v_isShared_4807_ = v_isSharedCheck_4817_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_name_4804_);
lean_inc(v_env_4803_);
lean_dec(v_e_4801_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4817_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4808_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4809_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__3, &l_Lean_Kernel_Exception_toMessageData___closed__3_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__3);
v___x_4810_ = l_Lean_MessageData_ofName(v_name_4804_);
if (v_isShared_4807_ == 0)
{
lean_ctor_set_tag(v___x_4806_, 7);
lean_ctor_set(v___x_4806_, 1, v___x_4810_);
lean_ctor_set(v___x_4806_, 0, v___x_4809_);
v___x_4812_ = v___x_4806_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4816_, 1, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4803_, v___x_4808_, v_opts_4802_, v___x_4814_);
return v___x_4815_;
}
}
}
case 1:
{
lean_object* v_env_4818_; lean_object* v_name_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4833_; 
v_env_4818_ = lean_ctor_get(v_e_4801_, 0);
v_name_4819_ = lean_ctor_get(v_e_4801_, 1);
v_isSharedCheck_4833_ = !lean_is_exclusive(v_e_4801_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4821_ = v_e_4801_;
v_isShared_4822_ = v_isSharedCheck_4833_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_name_4819_);
lean_inc(v_env_4818_);
lean_dec(v_e_4801_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4833_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4823_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4824_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__7, &l_Lean_Kernel_Exception_toMessageData___closed__7_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__7);
v___x_4825_ = 1;
v___x_4826_ = l_Lean_MessageData_ofConstName(v_name_4819_, v___x_4825_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set_tag(v___x_4821_, 7);
lean_ctor_set(v___x_4821_, 1, v___x_4826_);
lean_ctor_set(v___x_4821_, 0, v___x_4824_);
v___x_4828_ = v___x_4821_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4824_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4829_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4828_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4818_, v___x_4823_, v_opts_4802_, v___x_4830_);
return v___x_4831_;
}
}
}
case 2:
{
lean_object* v_env_4834_; lean_object* v_decl_4835_; lean_object* v_givenType_4836_; lean_object* v___x_4837_; 
v_env_4834_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4834_);
v_decl_4835_ = lean_ctor_get(v_e_4801_, 1);
lean_inc(v_decl_4835_);
v_givenType_4836_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_givenType_4836_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4837_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
switch(lean_obj_tag(v_decl_4835_))
{
case 1:
{
lean_object* v_val_4838_; lean_object* v_toConstantVal_4839_; lean_object* v_name_4840_; lean_object* v_type_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_val_4838_ = lean_ctor_get(v_decl_4835_, 0);
lean_inc_ref(v_val_4838_);
lean_dec_ref_known(v_decl_4835_, 1);
v_toConstantVal_4839_ = lean_ctor_get(v_val_4838_, 0);
lean_inc_ref(v_toConstantVal_4839_);
lean_dec_ref(v_val_4838_);
v_name_4840_ = lean_ctor_get(v_toConstantVal_4839_, 0);
lean_inc(v_name_4840_);
v_type_4841_ = lean_ctor_get(v_toConstantVal_4839_, 2);
lean_inc_ref(v_type_4841_);
lean_dec_ref(v_toConstantVal_4839_);
v___x_4842_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4836_, v_name_4840_, v_type_4841_);
v___x_4843_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4834_, v___x_4837_, v_opts_4802_, v___x_4842_);
return v___x_4843_;
}
case 2:
{
lean_object* v_val_4844_; lean_object* v_toConstantVal_4845_; lean_object* v_name_4846_; lean_object* v_type_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v_val_4844_ = lean_ctor_get(v_decl_4835_, 0);
lean_inc_ref(v_val_4844_);
lean_dec_ref_known(v_decl_4835_, 1);
v_toConstantVal_4845_ = lean_ctor_get(v_val_4844_, 0);
lean_inc_ref(v_toConstantVal_4845_);
lean_dec_ref(v_val_4844_);
v_name_4846_ = lean_ctor_get(v_toConstantVal_4845_, 0);
lean_inc(v_name_4846_);
v_type_4847_ = lean_ctor_get(v_toConstantVal_4845_, 2);
lean_inc_ref(v_type_4847_);
lean_dec_ref(v_toConstantVal_4845_);
v___x_4848_ = l_Lean_Kernel_Exception_toMessageData___lam__0(v_givenType_4836_, v_name_4846_, v_type_4847_);
v___x_4849_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4834_, v___x_4837_, v_opts_4802_, v___x_4848_);
return v___x_4849_;
}
default: 
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
lean_dec_ref(v_givenType_4836_);
lean_dec(v_decl_4835_);
v___x_4850_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__10, &l_Lean_Kernel_Exception_toMessageData___closed__10_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__10);
v___x_4851_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4834_, v___x_4837_, v_opts_4802_, v___x_4850_);
return v___x_4851_;
}
}
}
case 3:
{
lean_object* v_env_4852_; lean_object* v_name_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v_env_4852_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4852_);
v_name_4853_ = lean_ctor_get(v_e_4801_, 1);
lean_inc(v_name_4853_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4854_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4855_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__12, &l_Lean_Kernel_Exception_toMessageData___closed__12_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__12);
v___x_4856_ = 1;
v___x_4857_ = l_Lean_MessageData_ofConstName(v_name_4853_, v___x_4856_);
v___x_4858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4855_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4858_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4852_, v___x_4854_, v_opts_4802_, v___x_4860_);
return v___x_4861_;
}
case 4:
{
lean_object* v_env_4862_; lean_object* v_name_4863_; lean_object* v_expr_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; 
v_env_4862_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4862_);
v_name_4863_ = lean_ctor_get(v_e_4801_, 1);
lean_inc(v_name_4863_);
v_expr_4864_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_expr_4864_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4865_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4866_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__14, &l_Lean_Kernel_Exception_toMessageData___closed__14_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__14);
v___x_4867_ = 1;
v___x_4868_ = l_Lean_MessageData_ofConstName(v_name_4863_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4866_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__16, &l_Lean_Kernel_Exception_toMessageData___closed__16_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__16);
v___x_4871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4869_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l_Lean_indentExpr(v_expr_4864_);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
v___x_4874_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4862_, v___x_4865_, v_opts_4802_, v___x_4873_);
return v___x_4874_;
}
case 5:
{
lean_object* v_env_4875_; lean_object* v_lctx_4876_; lean_object* v_expr_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v_env_4875_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4875_);
v_lctx_4876_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4876_);
v_expr_4877_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_expr_4877_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4878_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__18, &l_Lean_Kernel_Exception_toMessageData___closed__18_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__18);
v___x_4879_ = l_Lean_indentExpr(v_expr_4877_);
v___x_4880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4878_);
lean_ctor_set(v___x_4880_, 1, v___x_4879_);
v___x_4881_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4875_, v_lctx_4876_, v_opts_4802_, v___x_4880_);
return v___x_4881_;
}
case 6:
{
lean_object* v_env_4882_; lean_object* v_lctx_4883_; lean_object* v_expr_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v_env_4882_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4882_);
v_lctx_4883_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4883_);
v_expr_4884_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_expr_4884_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4885_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__20, &l_Lean_Kernel_Exception_toMessageData___closed__20_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__20);
v___x_4886_ = l_Lean_indentExpr(v_expr_4884_);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
v___x_4888_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4882_, v_lctx_4883_, v_opts_4802_, v___x_4887_);
return v___x_4888_;
}
case 7:
{
lean_object* v_env_4889_; lean_object* v_lctx_4890_; lean_object* v_name_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; 
v_env_4889_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4889_);
v_lctx_4890_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4890_);
v_name_4891_ = lean_ctor_get(v_e_4801_, 2);
lean_inc(v_name_4891_);
lean_dec_ref_known(v_e_4801_, 5);
v___x_4892_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__22, &l_Lean_Kernel_Exception_toMessageData___closed__22_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__22);
v___x_4893_ = l_Lean_MessageData_ofName(v_name_4891_);
v___x_4894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4894_, 0, v___x_4892_);
lean_ctor_set(v___x_4894_, 1, v___x_4893_);
v___x_4895_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__5, &l_Lean_Kernel_Exception_toMessageData___closed__5_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__5);
v___x_4896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4894_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4889_, v_lctx_4890_, v_opts_4802_, v___x_4896_);
return v___x_4897_;
}
case 8:
{
lean_object* v_env_4898_; lean_object* v_lctx_4899_; lean_object* v_expr_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v_env_4898_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4898_);
v_lctx_4899_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4899_);
v_expr_4900_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_expr_4900_);
lean_dec_ref_known(v_e_4801_, 4);
v___x_4901_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__24, &l_Lean_Kernel_Exception_toMessageData___closed__24_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__24);
v___x_4902_ = l_Lean_indentExpr(v_expr_4900_);
v___x_4903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4901_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4898_, v_lctx_4899_, v_opts_4802_, v___x_4903_);
return v___x_4904_;
}
case 9:
{
lean_object* v_env_4905_; lean_object* v_lctx_4906_; lean_object* v_app_4907_; lean_object* v_funType_4908_; lean_object* v_argType_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_env_4905_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4905_);
v_lctx_4906_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4906_);
v_app_4907_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_app_4907_);
v_funType_4908_ = lean_ctor_get(v_e_4801_, 3);
lean_inc_ref(v_funType_4908_);
v_argType_4909_ = lean_ctor_get(v_e_4801_, 4);
lean_inc_ref(v_argType_4909_);
lean_dec_ref_known(v_e_4801_, 5);
v___x_4910_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__26, &l_Lean_Kernel_Exception_toMessageData___closed__26_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__26);
v___x_4911_ = l_Lean_indentExpr(v_app_4907_);
v___x_4912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4912_, 0, v___x_4910_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
v___x_4913_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__28, &l_Lean_Kernel_Exception_toMessageData___closed__28_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__28);
v___x_4914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4912_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = l_Lean_indentExpr(v_argType_4909_);
v___x_4916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
v___x_4917_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__30, &l_Lean_Kernel_Exception_toMessageData___closed__30_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__30);
v___x_4918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4916_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
v___x_4919_ = l_Lean_indentExpr(v_funType_4908_);
v___x_4920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4918_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4905_, v_lctx_4906_, v_opts_4802_, v___x_4920_);
return v___x_4921_;
}
case 10:
{
lean_object* v_env_4922_; lean_object* v_lctx_4923_; lean_object* v_proj_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v_env_4922_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4922_);
v_lctx_4923_ = lean_ctor_get(v_e_4801_, 1);
lean_inc_ref(v_lctx_4923_);
v_proj_4924_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_proj_4924_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4925_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__32, &l_Lean_Kernel_Exception_toMessageData___closed__32_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__32);
v___x_4926_ = l_Lean_indentExpr(v_proj_4924_);
v___x_4927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
v___x_4928_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4922_, v_lctx_4923_, v_opts_4802_, v___x_4927_);
return v___x_4928_;
}
case 11:
{
lean_object* v_env_4929_; lean_object* v_name_4930_; lean_object* v_type_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; uint8_t v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v_env_4929_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_env_4929_);
v_name_4930_ = lean_ctor_get(v_e_4801_, 1);
lean_inc(v_name_4930_);
v_type_4931_ = lean_ctor_get(v_e_4801_, 2);
lean_inc_ref(v_type_4931_);
lean_dec_ref_known(v_e_4801_, 3);
v___x_4932_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__1, &l_Lean_Kernel_Exception_toMessageData___closed__1_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__1);
v___x_4933_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__34, &l_Lean_Kernel_Exception_toMessageData___closed__34_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__34);
v___x_4934_ = 1;
v___x_4935_ = l_Lean_MessageData_ofConstName(v_name_4930_, v___x_4934_);
v___x_4936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4933_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__36, &l_Lean_Kernel_Exception_toMessageData___closed__36_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__36);
v___x_4938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = l_Lean_indentExpr(v_type_4931_);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4938_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
v___x_4941_ = l___private_Lean_Message_0__Lean_Kernel_Exception_mkCtx(v_env_4929_, v___x_4932_, v_opts_4802_, v___x_4940_);
return v___x_4941_;
}
case 12:
{
lean_object* v_msg_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; 
lean_dec_ref(v_opts_4802_);
v_msg_4942_ = lean_ctor_get(v_e_4801_, 0);
lean_inc_ref(v_msg_4942_);
lean_dec_ref_known(v_e_4801_, 1);
v___x_4943_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__38, &l_Lean_Kernel_Exception_toMessageData___closed__38_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__38);
v___x_4944_ = l_Lean_stringToMessageData(v_msg_4942_);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
return v___x_4945_;
}
case 13:
{
lean_object* v___x_4946_; 
lean_dec_ref(v_opts_4802_);
v___x_4946_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__41, &l_Lean_Kernel_Exception_toMessageData___closed__41_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__41);
return v___x_4946_;
}
case 14:
{
lean_object* v___x_4947_; 
lean_dec_ref(v_opts_4802_);
v___x_4947_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__44, &l_Lean_Kernel_Exception_toMessageData___closed__44_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__44);
return v___x_4947_;
}
case 15:
{
lean_object* v___x_4948_; 
lean_dec_ref(v_opts_4802_);
v___x_4948_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__47, &l_Lean_Kernel_Exception_toMessageData___closed__47_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__47);
return v___x_4948_;
}
default: 
{
lean_object* v___x_4949_; 
lean_dec_ref(v_opts_4802_);
v___x_4949_ = lean_obj_once(&l_Lean_Kernel_Exception_toMessageData___closed__50, &l_Lean_Kernel_Exception_toMessageData___closed__50_once, _init_l_Lean_Kernel_Exception_toMessageData___closed__50);
return v___x_4949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem___redArg(lean_object* v_inst_4950_, lean_object* v_e_4951_, lean_object* v_cls_4952_){
_start:
{
lean_object* v___x_4953_; double v___x_4954_; uint8_t v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4953_ = lean_box(0);
v___x_4954_ = lean_float_once(&l_Lean_MessageData_formatAux___closed__9, &l_Lean_MessageData_formatAux___closed__9_once, _init_l_Lean_MessageData_formatAux___closed__9);
v___x_4955_ = 1;
v___x_4956_ = ((lean_object*)(l_Lean_mkErrorStringWithPos___closed__2));
v___x_4957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4957_, 0, v_cls_4952_);
lean_ctor_set(v___x_4957_, 1, v___x_4953_);
lean_ctor_set(v___x_4957_, 2, v___x_4956_);
lean_ctor_set_float(v___x_4957_, sizeof(void*)*3, v___x_4954_);
lean_ctor_set_float(v___x_4957_, sizeof(void*)*3 + 8, v___x_4954_);
lean_ctor_set_uint8(v___x_4957_, sizeof(void*)*3 + 16, v___x_4955_);
v___x_4958_ = lean_apply_1(v_inst_4950_, v_e_4951_);
v___x_4959_ = ((lean_object*)(l_Lean_stringToMessageData___closed__0));
v___x_4960_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4957_);
lean_ctor_set(v___x_4960_, 1, v___x_4958_);
lean_ctor_set(v___x_4960_, 2, v___x_4959_);
return v___x_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_toTraceElem(lean_object* v_00_u03b1_4961_, lean_object* v_inst_4962_, lean_object* v_e_4963_, lean_object* v_cls_4964_){
_start:
{
lean_object* v___x_4965_; 
v___x_4965_ = l_Lean_toTraceElem___redArg(v_inst_4962_, v_e_4963_, v_cls_4964_);
return v___x_4965_;
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
