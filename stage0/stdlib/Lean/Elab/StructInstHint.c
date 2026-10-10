// Lean compiler output
// Module: Lean.Elab.StructInstHint
// Imports: public import Lean.Meta.Hint import Init.Data.String.OrderInstances
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_format_inputWidth;
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
static const lean_string_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structInst"};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 43, 73, 62, 118, 124, 31, 28)}};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 221, 19, 63, 207, 193, 180, 154)}};
static const lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object*);
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Add missing fields"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__0_value)}};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1_value;
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Add missing fields:"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3;
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__4_value)}};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5_value;
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6_value;
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7_value;
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(lean_object* v_stx_10_){
_start:
{
lean_object* v___y_12_; lean_object* v___y_13_; lean_object* v___y_14_; uint8_t v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; uint8_t v___y_26_; lean_object* v___y_27_; uint8_t v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v_fst_39_; uint8_t v_snd_40_; lean_object* v___x_67_; 
v___x_67_ = l_Lean_Syntax_getHeadInfo(v_stx_10_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
lean_dec_ref_known(v___x_67_, 4);
lean_inc(v_stx_10_);
v___x_68_ = l_Lean_Syntax_getKind(v_stx_10_);
v___x_69_ = ((lean_object*)(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f___closed__4));
v___x_70_ = lean_name_eq(v___x_68_, v___x_69_);
lean_dec(v___x_68_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_stx_10_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_72_);
v___x_74_ = l_Lean_Syntax_getArg(v___x_73_, v___x_72_);
lean_dec(v___x_73_);
if (lean_obj_tag(v___x_74_) == 0)
{
if (v___x_70_ == 0)
{
v_fst_39_ = v___x_74_;
v_snd_40_ = v___x_70_;
goto v___jp_38_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_75_);
v___x_77_ = 0;
v_fst_39_ = v___x_76_;
v_snd_40_ = v___x_77_;
goto v___jp_38_;
}
}
else
{
v_fst_39_ = v___x_74_;
v_snd_40_ = v___x_70_;
goto v___jp_38_;
}
}
}
else
{
lean_object* v___x_78_; 
lean_dec(v___x_67_);
lean_dec(v_stx_10_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
v___jp_11_:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_20_, 0, v___y_17_);
lean_ctor_set(v___x_20_, 1, v___y_19_);
lean_ctor_set(v___x_20_, 2, v___y_16_);
lean_ctor_set(v___x_20_, 3, v___y_18_);
lean_ctor_set(v___x_20_, 4, v___y_12_);
lean_ctor_set(v___x_20_, 5, v___y_14_);
lean_ctor_set(v___x_20_, 6, v___y_13_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*7, v___y_15_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
v___jp_22_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_31_ = lean_array_get_size(v___y_27_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v___x_31_, v___x_32_);
v___x_34_ = lean_nat_dec_lt(v___x_33_, v___x_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___x_33_);
lean_dec_ref(v___y_27_);
v___x_35_ = lean_box(0);
v___y_12_ = v___y_23_;
v___y_13_ = v___y_24_;
v___y_14_ = v___y_25_;
v___y_15_ = v___y_26_;
v___y_16_ = v___x_31_;
v___y_17_ = v___y_30_;
v___y_18_ = v___y_29_;
v___y_19_ = v___x_35_;
goto v___jp_11_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_fget(v___y_27_, v___x_33_);
lean_dec(v___x_33_);
lean_dec_ref(v___y_27_);
v___x_37_ = l_Lean_Syntax_getTailPos_x3f(v___x_36_, v___y_28_);
lean_dec(v___x_36_);
v___y_12_ = v___y_23_;
v___y_13_ = v___y_24_;
v___y_14_ = v___y_25_;
v___y_15_ = v___y_26_;
v___y_16_ = v___x_31_;
v___y_17_ = v___y_30_;
v___y_18_ = v___y_29_;
v___y_19_ = v___x_37_;
goto v___jp_11_;
}
}
v___jp_38_:
{
uint8_t v___x_41_; lean_object* v___x_42_; 
v___x_41_ = 0;
v___x_42_ = l_Lean_Syntax_getPos_x3f(v_fst_39_, v___x_41_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v___x_43_; 
lean_dec(v_fst_39_);
lean_dec(v_stx_10_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_45_; 
v_val_44_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_val_44_);
lean_dec_ref_known(v___x_42_, 1);
v___x_45_ = l_Lean_Syntax_getTailPos_x3f(v_fst_39_, v___x_41_);
lean_dec(v_fst_39_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v___x_46_; 
lean_dec(v_val_44_);
lean_dec(v_stx_10_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
lean_object* v_val_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_val_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_47_);
lean_dec_ref_known(v___x_45_, 1);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_48_);
v___x_50_ = l_Lean_Syntax_getPos_x3f(v___x_49_, v___x_41_);
lean_dec(v___x_49_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v___x_51_; 
lean_dec(v_val_47_);
lean_dec(v_val_44_);
lean_dec(v_stx_10_);
v___x_51_ = lean_box(0);
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_val_52_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_val_52_);
lean_dec_ref_known(v___x_50_, 1);
v___x_53_ = lean_unsigned_to_nat(5u);
v___x_54_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_53_);
v___x_55_ = l_Lean_Syntax_getPos_x3f(v___x_54_, v___x_41_);
lean_dec(v___x_54_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v___x_56_; 
lean_dec(v_val_52_);
lean_dec(v_val_47_);
lean_dec(v_val_44_);
lean_dec(v_stx_10_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v_val_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v_val_57_ = lean_ctor_get(v___x_55_, 0);
lean_inc(v_val_57_);
lean_dec_ref_known(v___x_55_, 1);
v___x_58_ = lean_unsigned_to_nat(2u);
v___x_59_ = l_Lean_Syntax_getArg(v_stx_10_, v___x_58_);
lean_dec(v_stx_10_);
v___x_60_ = l_Lean_Syntax_getArg(v___x_59_, v___x_48_);
lean_dec(v___x_59_);
v___x_61_ = l_Lean_Syntax_getSepArgs(v___x_60_);
lean_dec(v___x_60_);
v___x_62_ = lean_array_get_size(v___x_61_);
v___x_63_ = lean_nat_dec_lt(v___x_48_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
v___y_23_ = v_val_44_;
v___y_24_ = v_val_57_;
v___y_25_ = v_val_47_;
v___y_26_ = v_snd_40_;
v___y_27_ = v___x_61_;
v___y_28_ = v___x_41_;
v___y_29_ = v_val_52_;
v___y_30_ = v___x_64_;
goto v___jp_22_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_array_fget_borrowed(v___x_61_, v___x_48_);
v___x_66_ = l_Lean_Syntax_getPos_x3f(v___x_65_, v___x_41_);
v___y_23_ = v_val_44_;
v___y_24_ = v_val_57_;
v___y_25_ = v_val_47_;
v___y_26_ = v_snd_40_;
v___y_27_ = v___x_61_;
v___y_28_ = v___x_41_;
v___y_29_ = v_val_52_;
v___y_30_ = v___x_66_;
goto v___jp_22_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(lean_object* v___x_79_, lean_object* v___x_80_, lean_object* v_s_81_, lean_object* v_a_82_, lean_object* v_b_83_){
_start:
{
lean_object* v___x_84_; uint8_t v_decide_85_; 
v___x_84_ = lean_nat_sub(v___x_79_, v___x_80_);
v_decide_85_ = lean_nat_dec_eq(v_a_82_, v___x_84_);
lean_dec(v___x_84_);
if (v_decide_85_ == 0)
{
lean_object* v___x_86_; uint32_t v___x_87_; uint32_t v___x_88_; uint8_t v___x_89_; 
v___x_86_ = lean_nat_add(v___x_80_, v_a_82_);
v___x_87_ = lean_string_utf8_get_fast(v_s_81_, v___x_86_);
v___x_88_ = 10;
v___x_89_ = lean_uint32_dec_eq(v___x_87_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_a_82_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_string_utf8_next_fast(v_s_81_, v___x_86_);
lean_dec(v___x_86_);
v___x_92_ = lean_nat_sub(v___x_91_, v___x_80_);
v_a_82_ = v___x_92_;
v_b_83_ = v___x_90_;
goto _start;
}
else
{
lean_object* v___x_94_; 
lean_dec(v___x_86_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_a_82_);
return v___x_94_;
}
}
else
{
lean_dec(v_a_82_);
lean_inc(v_b_83_);
return v_b_83_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg___boxed(lean_object* v___x_95_, lean_object* v___x_96_, lean_object* v_s_97_, lean_object* v_a_98_, lean_object* v_b_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_95_, v___x_96_, v_s_97_, v_a_98_, v_b_99_);
lean_dec(v_b_99_);
lean_dec_ref(v_s_97_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(lean_object* v_s_101_, lean_object* v_p_102_){
_start:
{
lean_object* v_searcher_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_searcher_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_string_utf8_byte_size(v_s_101_);
lean_inc_ref(v_s_101_);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v_s_101_);
lean_ctor_set(v___x_105_, 1, v_searcher_103_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
v___x_106_ = l_String_Slice_pos_x21(v___x_105_, v_p_102_);
lean_dec_ref_known(v___x_105_, 3);
v___x_107_ = lean_box(0);
v___x_108_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_104_, v___x_106_, v_s_101_, v_searcher_103_, v___x_107_);
lean_dec_ref(v_s_101_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_nat_sub(v___x_104_, v___x_106_);
v___x_110_ = lean_nat_add(v___x_106_, v___x_109_);
lean_dec(v___x_109_);
lean_dec(v___x_106_);
return v___x_110_;
}
else
{
lean_object* v_val_111_; lean_object* v___x_112_; 
v_val_111_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v___x_108_, 1);
v___x_112_ = lean_nat_add(v___x_106_, v_val_111_);
lean_dec(v_val_111_);
lean_dec(v___x_106_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd___boxed(lean_object* v_s_113_, lean_object* v_p_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_s_113_, v_p_114_);
lean_dec(v_p_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0(lean_object* v___x_116_, lean_object* v___x_117_, lean_object* v___x_118_, lean_object* v_s_119_, lean_object* v_inst_120_, lean_object* v_R_121_, lean_object* v_a_122_, lean_object* v_b_123_, lean_object* v_c_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___redArg(v___x_116_, v___x_117_, v_s_119_, v_a_122_, v_b_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0___boxed(lean_object* v___x_126_, lean_object* v___x_127_, lean_object* v___x_128_, lean_object* v_s_129_, lean_object* v_inst_130_, lean_object* v_R_131_, lean_object* v_a_132_, lean_object* v_b_133_, lean_object* v_c_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd_spec__0(v___x_126_, v___x_127_, v___x_128_, v_s_129_, v_inst_130_, v_R_131_, v_a_132_, v_b_133_, v_c_134_);
lean_dec(v_b_133_);
lean_dec_ref(v_s_129_);
lean_dec_ref(v___x_128_);
lean_dec(v___x_127_);
lean_dec(v___x_126_);
return v_res_135_;
}
}
lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(lean_object* v_stx_139_, lean_object* v_view_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_numFields_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_numFields_143_ = lean_ctor_get(v_view_140_, 2);
v___x_144_ = lean_unsigned_to_nat(2u);
v___x_145_ = lean_nat_dec_le(v___x_144_, v_numFields_143_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box(v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_rawFields_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_lastInterveningSepIdx_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_148_ = l_Lean_Syntax_getArg(v_stx_139_, v___x_144_);
v___x_149_ = lean_unsigned_to_nat(0u);
v_rawFields_150_ = l_Lean_Syntax_getArg(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___x_151_ = l_Lean_Syntax_getNumArgs(v_rawFields_150_);
v___x_152_ = lean_nat_sub(v___x_151_, v___x_144_);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v___x_151_, v___x_153_);
lean_dec(v___x_151_);
v___x_155_ = lean_nat_mod(v___x_154_, v___x_144_);
lean_dec(v___x_154_);
v_lastInterveningSepIdx_156_ = lean_nat_sub(v___x_152_, v___x_155_);
lean_dec(v___x_155_);
lean_dec(v___x_152_);
v___x_157_ = l_Lean_Syntax_getArg(v_rawFields_150_, v_lastInterveningSepIdx_156_);
v___x_158_ = l_Lean_Syntax_getKind(v___x_157_);
v___x_159_ = ((lean_object*)(l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__1));
v___x_160_ = lean_name_eq(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_lastInterveningSepIdx_156_);
lean_dec(v_rawFields_150_);
v___x_161_ = lean_box(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; 
v___x_163_ = lean_nat_sub(v_lastInterveningSepIdx_156_, v___x_153_);
v___x_164_ = l_Lean_Syntax_getArg(v_rawFields_150_, v___x_163_);
lean_dec(v___x_163_);
v___x_165_ = 0;
v___x_166_ = l_Lean_Syntax_getPos_x3f(v___x_164_, v___x_165_);
lean_dec(v___x_164_);
if (lean_obj_tag(v___x_166_) == 1)
{
lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_211_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_211_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_211_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_211_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_nat_add(v_lastInterveningSepIdx_156_, v___x_153_);
lean_dec(v_lastInterveningSepIdx_156_);
v___x_172_ = l_Lean_Syntax_getArg(v_rawFields_150_, v___x_171_);
lean_dec(v___x_171_);
lean_dec(v_rawFields_150_);
v___x_173_ = l_Lean_Syntax_getPos_x3f(v___x_172_, v___x_165_);
if (lean_obj_tag(v___x_173_) == 1)
{
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_169_);
v_val_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_206_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_206_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_206_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Syntax_getTailPos_x3f(v___x_172_, v___x_165_);
lean_dec(v___x_172_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_200_; 
lean_del_object(v___x_176_);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_200_ == 0)
{
lean_object* v_unused_201_; 
v_unused_201_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_201_);
v___x_180_ = v___x_178_;
v_isShared_181_ = v_isSharedCheck_200_;
goto v_resetjp_179_;
}
else
{
lean_dec(v___x_178_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_200_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_toCold_182_; lean_object* v_fileMap_183_; lean_object* v___x_184_; lean_object* v_line_185_; lean_object* v_character_186_; lean_object* v___x_187_; lean_object* v_line_188_; lean_object* v_character_189_; uint8_t v___x_190_; 
v_toCold_182_ = lean_ctor_get(v_a_141_, 0);
v_fileMap_183_ = lean_ctor_get(v_toCold_182_, 1);
lean_inc_ref_n(v_fileMap_183_, 2);
v___x_184_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_183_, v_val_167_);
lean_dec(v_val_167_);
v_line_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_line_185_);
v_character_186_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_character_186_);
lean_dec_ref(v___x_184_);
v___x_187_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_183_, v_val_174_);
lean_dec(v_val_174_);
v_line_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_line_188_);
v_character_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_character_189_);
lean_dec_ref(v___x_187_);
v___x_190_ = lean_nat_dec_eq(v_line_188_, v_line_185_);
lean_dec(v_line_185_);
lean_dec(v_line_188_);
if (v___x_190_ == 0)
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_191_ = lean_nat_dec_lt(v_character_189_, v_character_186_);
lean_dec(v_character_186_);
lean_dec(v_character_189_);
v___x_192_ = lean_box(v___x_191_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
lean_ctor_set(v___x_180_, 0, v___x_192_);
v___x_194_ = v___x_180_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_198_; 
lean_dec(v_character_189_);
lean_dec(v_character_186_);
v___x_196_ = lean_box(v___x_145_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
lean_ctor_set(v___x_180_, 0, v___x_196_);
v___x_198_ = v___x_180_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec(v___x_178_);
lean_dec(v_val_174_);
lean_dec(v_val_167_);
v___x_202_ = lean_box(v___x_165_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
lean_ctor_set(v___x_176_, 0, v___x_202_);
v___x_204_ = v___x_176_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec(v___x_173_);
lean_dec(v___x_172_);
lean_dec(v_val_167_);
v___x_207_ = lean_box(v___x_165_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 0);
lean_ctor_set(v___x_169_, 0, v___x_207_);
v___x_209_ = v___x_169_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v___x_166_);
lean_dec(v_lastInterveningSepIdx_156_);
lean_dec(v_rawFields_150_);
v___x_212_ = lean_box(v___x_165_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_139_ = stack[0].m_obj;
lean_object* v_view_140_ = stack[1].m_obj;
lean_object* v_a_141_ = stack[2].m_obj;
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_139_, v_view_140_, v_a_141_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___boxed(lean_object* v_stx_215_, lean_object* v_view_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_215_, v_view_216_, v_a_217_);
lean_dec_ref(v_a_217_);
lean_dec_ref(v_view_216_);
lean_dec(v_stx_215_);
return v_res_219_;
}
}
lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(lean_object* v_stx_220_, lean_object* v_view_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_220_, v_view_221_, v_a_224_);
return v___x_227_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_220_ = stack[0].m_obj;
lean_object* v_view_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_res_228_;
v_res_228_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(v_stx_220_, v_view_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___boxed(lean_object* v_stx_229_, lean_object* v_view_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(v_stx_229_, v_view_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec_ref(v_view_230_);
lean_dec(v_stx_229_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object* v_opts_237_, lean_object* v_opt_238_){
_start:
{
lean_object* v_name_239_; lean_object* v_defValue_240_; lean_object* v_map_241_; lean_object* v___x_242_; 
v_name_239_ = lean_ctor_get(v_opt_238_, 0);
v_defValue_240_ = lean_ctor_get(v_opt_238_, 1);
v_map_241_ = lean_ctor_get(v_opts_237_, 0);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_241_, v_name_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_inc(v_defValue_240_);
return v_defValue_240_;
}
else
{
lean_object* v_val_243_; 
v_val_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v___x_242_, 1);
if (lean_obj_tag(v_val_243_) == 3)
{
lean_object* v_v_244_; 
v_v_244_ = lean_ctor_get(v_val_243_, 0);
lean_inc(v_v_244_);
lean_dec_ref_known(v_val_243_, 1);
return v_v_244_;
}
else
{
lean_dec(v_val_243_);
lean_inc(v_defValue_240_);
return v_defValue_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object* v_opts_245_, lean_object* v_opt_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_opts_245_, v_opt_246_);
lean_dec_ref(v_opt_246_);
lean_dec_ref(v_opts_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object* v_msg_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = l_String_instInhabitedSlice;
v___x_250_ = lean_panic_fn_borrowed(v___x_249_, v_msg_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object* v_x_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0));
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(v_x_254_);
lean_dec_ref(v_x_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object* v_fileMap_256_, lean_object* v_p_257_){
_start:
{
lean_object* v___x_258_; lean_object* v_character_259_; 
v___x_258_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_256_, v_p_257_);
v_character_259_ = lean_ctor_get(v___x_258_, 1);
lean_inc(v_character_259_);
lean_dec_ref(v___x_258_);
return v_character_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object* v_fileMap_260_, lean_object* v_p_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_260_, v_p_261_);
lean_dec(v_p_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(lean_object* v___x_263_, lean_object* v_j_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_zero_266_; uint8_t v_isZero_267_; 
v_zero_266_ = lean_unsigned_to_nat(0u);
v_isZero_267_ = lean_nat_dec_eq(v_j_264_, v_zero_266_);
if (v_isZero_267_ == 1)
{
lean_dec(v_j_264_);
return v_a_265_;
}
else
{
lean_object* v_one_268_; lean_object* v_n_269_; lean_object* v___x_270_; 
v_one_268_ = lean_unsigned_to_nat(1u);
v_n_269_ = lean_nat_sub(v_j_264_, v_one_268_);
lean_dec(v_j_264_);
v___x_270_ = lean_string_utf8_next(v___x_263_, v_a_265_);
lean_dec(v_a_265_);
v_j_264_ = v_n_269_;
v_a_265_ = v___x_270_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg___boxed(lean_object* v___x_272_, lean_object* v_j_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v___x_272_, v_j_273_, v_a_274_);
lean_dec_ref(v___x_272_);
return v_res_275_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object* v_as_278_, size_t v_i_279_, size_t v_stop_280_, lean_object* v_b_281_){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = lean_usize_dec_eq(v_i_279_, v_stop_280_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; size_t v___x_290_; size_t v___x_291_; 
v___x_283_ = lean_array_uget_borrowed(v_as_278_, v_i_279_);
v___x_284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___closed__0));
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v_b_281_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_box(1);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_inc(v___x_283_);
v___x_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_288_, 0, v___x_283_);
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_i_279_, v___x_290_);
v_i_279_ = v___x_291_;
v_b_281_ = v___x_289_;
goto _start;
}
else
{
return v_b_281_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_278_ = stack[0].m_obj;
size_t v_i_279_ = stack[1].m_num;
size_t v_stop_280_ = stack[2].m_num;
lean_object* v_b_281_ = stack[3].m_obj;
lean_object* v_res_293_;
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_as_278_, v_i_279_, v_stop_280_, v_b_281_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___boxed(lean_object* v_as_294_, lean_object* v_i_295_, lean_object* v_stop_296_, lean_object* v_b_297_){
_start:
{
size_t v_i_boxed_298_; size_t v_stop_boxed_299_; lean_object* v_res_300_; 
v_i_boxed_298_ = lean_unbox_usize(v_i_295_);
lean_dec(v_i_295_);
v_stop_boxed_299_ = lean_unbox_usize(v_stop_296_);
lean_dec(v_stop_296_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_as_294_, v_i_boxed_298_, v_stop_boxed_299_, v_b_297_);
lean_dec_ref(v_as_294_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6_spec__7(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_dec(v_x_301_);
return v_x_302_;
}
else
{
lean_object* v_head_304_; lean_object* v_tail_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_315_; 
v_head_304_ = lean_ctor_get(v_x_303_, 0);
v_tail_305_ = lean_ctor_get(v_x_303_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_315_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_tail_305_);
lean_inc(v_head_304_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_315_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
lean_inc(v_x_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 5);
lean_ctor_set(v___x_307_, 1, v_x_301_);
lean_ctor_set(v___x_307_, 0, v_x_302_);
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_x_302_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_x_301_);
v___x_310_ = v_reuseFailAlloc_314_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_311_, 0, v_head_304_);
v___x_312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v_x_302_ = v___x_312_;
v_x_303_ = v_tail_305_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object* v_x_316_, lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
lean_object* v___x_318_; 
lean_dec(v_x_317_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
else
{
lean_object* v_tail_319_; 
v_tail_319_ = lean_ctor_get(v_x_316_, 1);
if (lean_obj_tag(v_tail_319_) == 0)
{
lean_object* v_head_320_; lean_object* v___x_321_; 
lean_dec(v_x_317_);
v_head_320_ = lean_ctor_get(v_x_316_, 0);
lean_inc(v_head_320_);
lean_dec_ref_known(v_x_316_, 2);
v___x_321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_321_, 0, v_head_320_);
return v___x_321_;
}
else
{
lean_object* v_head_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
lean_inc(v_tail_319_);
v_head_322_ = lean_ctor_get(v_x_316_, 0);
lean_inc(v_head_322_);
lean_dec_ref_known(v_x_316_, 2);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v_head_322_);
v___x_324_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6_spec__7(v_x_317_, v___x_323_, v_tail_319_);
return v___x_324_;
}
}
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(lean_object* v_o_328_, lean_object* v_k_329_, uint8_t v_v_330_){
_start:
{
lean_object* v_map_331_; uint8_t v_hasTrace_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_346_; 
v_map_331_ = lean_ctor_get(v_o_328_, 0);
v_hasTrace_332_ = lean_ctor_get_uint8(v_o_328_, sizeof(void*)*1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_o_328_);
if (v_isSharedCheck_346_ == 0)
{
v___x_334_ = v_o_328_;
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_map_331_);
lean_dec(v_o_328_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_346_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_336_, 0, v_v_330_);
lean_inc(v_k_329_);
v___x_337_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_329_, v___x_336_, v_map_331_);
if (v_hasTrace_332_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_341_; 
v___x_338_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__1));
v___x_339_ = l_Lean_Name_isPrefixOf(v___x_338_, v_k_329_);
lean_dec(v_k_329_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_341_ = v___x_334_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_337_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*1, v___x_339_);
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec(v_k_329_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_344_ = v___x_334_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_345_, sizeof(void*)*1, v_hasTrace_332_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_328_ = stack[0].m_obj;
lean_object* v_k_329_ = stack[1].m_obj;
uint8_t v_v_330_ = stack[2].m_num;
lean_object* v_res_347_;
v_res_347_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(v_o_328_, v_k_329_, v_v_330_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___boxed(lean_object* v_o_348_, lean_object* v_k_349_, lean_object* v_v_350_){
_start:
{
uint8_t v_v_boxed_351_; lean_object* v_res_352_; 
v_v_boxed_351_ = lean_unbox(v_v_350_);
v_res_352_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(v_o_348_, v_k_349_, v_v_boxed_351_);
return v_res_352_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object* v_opts_353_, lean_object* v_opt_354_, uint8_t v_val_355_){
_start:
{
lean_object* v_name_356_; lean_object* v___x_357_; 
v_name_356_ = lean_ctor_get(v_opt_354_, 0);
lean_inc(v_name_356_);
lean_dec_ref(v_opt_354_);
v___x_357_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(v_opts_353_, v_name_356_, v_val_355_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_353_ = stack[0].m_obj;
lean_object* v_opt_354_ = stack[1].m_obj;
uint8_t v_val_355_ = stack[2].m_num;
lean_object* v_res_358_;
v_res_358_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_353_, v_opt_354_, v_val_355_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object* v_opts_359_, lean_object* v_opt_360_, lean_object* v_val_361_){
_start:
{
uint8_t v_val_boxed_362_; lean_object* v_res_363_; 
v_val_boxed_362_ = lean_unbox(v_val_361_);
v_res_363_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_359_, v_opt_360_, v_val_boxed_362_);
return v_res_363_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
return v___x_372_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(size_t v_sz_374_, size_t v_i_375_, lean_object* v_bs_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = lean_usize_dec_lt(v_i_375_, v_sz_374_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v_bs_376_);
return v___x_383_;
}
else
{
lean_object* v_v_384_; lean_object* v_fst_385_; lean_object* v_snd_386_; lean_object* v___x_387_; lean_object* v_bs_x27_388_; lean_object* v_value_390_; 
v_v_384_ = lean_array_uget_borrowed(v_bs_376_, v_i_375_);
v_fst_385_ = lean_ctor_get(v_v_384_, 0);
lean_inc(v_fst_385_);
v_snd_386_ = lean_ctor_get(v_v_384_, 1);
lean_inc(v_snd_386_);
v___x_387_ = lean_unsigned_to_nat(0u);
v_bs_x27_388_ = lean_array_uset(v_bs_376_, v_i_375_, v___x_387_);
if (lean_obj_tag(v_snd_386_) == 1)
{
lean_object* v_toCold_399_; lean_object* v_val_400_; lean_object* v_currRecDepth_401_; lean_object* v_ref_402_; uint8_t v_suppressElabErrors_403_; uint8_t v_isRecordingDeps_404_; lean_object* v_fileName_405_; lean_object* v_fileMap_406_; lean_object* v_options_407_; lean_object* v_currNamespace_408_; lean_object* v_openDecls_409_; lean_object* v_initHeartbeats_410_; lean_object* v_maxHeartbeats_411_; lean_object* v_quotContext_412_; lean_object* v_currMacroScope_413_; lean_object* v_cancelTk_x3f_414_; lean_object* v_inheritedTraceOptions_415_; lean_object* v___x_416_; uint16_t v___y_418_; lean_object* v___y_419_; lean_object* v_fileName_420_; lean_object* v_fileMap_421_; lean_object* v_currNamespace_422_; lean_object* v_openDecls_423_; lean_object* v_initHeartbeats_424_; lean_object* v_maxHeartbeats_425_; lean_object* v_quotContext_426_; lean_object* v_currMacroScope_427_; lean_object* v_cancelTk_x3f_428_; lean_object* v_inheritedTraceOptions_429_; lean_object* v_currRecDepth_430_; lean_object* v_ref_431_; uint8_t v_suppressElabErrors_432_; uint8_t v_isRecordingDeps_433_; lean_object* v___y_434_; uint16_t v___y_463_; lean_object* v___y_464_; uint8_t v___y_465_; uint16_t v___y_488_; lean_object* v___y_489_; uint8_t v___y_490_; uint8_t v___y_491_; uint16_t v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; uint8_t v___y_496_; lean_object* v___y_498_; 
v_toCold_399_ = lean_ctor_get(v___y_379_, 0);
v_val_400_ = lean_ctor_get(v_snd_386_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_snd_386_, 1);
v_currRecDepth_401_ = lean_ctor_get(v___y_379_, 1);
v_ref_402_ = lean_ctor_get(v___y_379_, 2);
v_suppressElabErrors_403_ = lean_ctor_get_uint8(v___y_379_, sizeof(void*)*3 + 2);
v_isRecordingDeps_404_ = lean_ctor_get_uint8(v___y_379_, sizeof(void*)*3 + 3);
v_fileName_405_ = lean_ctor_get(v_toCold_399_, 0);
v_fileMap_406_ = lean_ctor_get(v_toCold_399_, 1);
v_options_407_ = lean_ctor_get(v_toCold_399_, 2);
v_currNamespace_408_ = lean_ctor_get(v_toCold_399_, 4);
v_openDecls_409_ = lean_ctor_get(v_toCold_399_, 5);
v_initHeartbeats_410_ = lean_ctor_get(v_toCold_399_, 6);
v_maxHeartbeats_411_ = lean_ctor_get(v_toCold_399_, 7);
v_quotContext_412_ = lean_ctor_get(v_toCold_399_, 8);
v_currMacroScope_413_ = lean_ctor_get(v_toCold_399_, 9);
v_cancelTk_x3f_414_ = lean_ctor_get(v_toCold_399_, 10);
v_inheritedTraceOptions_415_ = lean_ctor_get(v_toCold_399_, 11);
v___x_416_ = lean_box(1);
if (v_isRecordingDeps_404_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_407_);
v___x_509_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_options_407_, v___x_508_, v_isRecordingDeps_404_);
v___y_498_ = v___x_509_;
goto v___jp_497_;
}
else
{
lean_object* v___x_510_; 
lean_inc_ref(v_options_407_);
v___x_510_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_407_);
v___y_498_ = v___x_510_;
goto v___jp_497_;
}
v___jp_417_:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_435_ = l_Lean_maxRecDepth;
v___x_436_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v___y_419_, v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_437_, 0, v_fileName_420_);
lean_ctor_set(v___x_437_, 1, v_fileMap_421_);
lean_ctor_set(v___x_437_, 2, v___y_419_);
lean_ctor_set(v___x_437_, 3, v___x_436_);
lean_ctor_set(v___x_437_, 4, v_currNamespace_422_);
lean_ctor_set(v___x_437_, 5, v_openDecls_423_);
lean_ctor_set(v___x_437_, 6, v_initHeartbeats_424_);
lean_ctor_set(v___x_437_, 7, v_maxHeartbeats_425_);
lean_ctor_set(v___x_437_, 8, v_quotContext_426_);
lean_ctor_set(v___x_437_, 9, v_currMacroScope_427_);
lean_ctor_set(v___x_437_, 10, v_cancelTk_x3f_428_);
lean_ctor_set(v___x_437_, 11, v_inheritedTraceOptions_429_);
lean_inc(v_ref_431_);
lean_inc(v_currRecDepth_430_);
v___x_438_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_currRecDepth_430_);
lean_ctor_set(v___x_438_, 2, v_ref_431_);
lean_ctor_set_uint16(v___x_438_, sizeof(void*)*3, v___y_418_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*3 + 2, v_suppressElabErrors_432_);
lean_ctor_set_uint8(v___x_438_, sizeof(void*)*3 + 3, v_isRecordingDeps_433_);
v___x_439_ = l_Lean_PrettyPrinter_delab(v_val_400_, v___x_416_, v___y_377_, v___y_378_, v___x_438_, v___y_434_);
lean_dec_ref_known(v___x_438_, 3);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2));
v___x_442_ = l_Lean_PrettyPrinter_ppCategory(v___x_441_, v_a_440_, v___y_379_, v___y_380_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = l_Std_Format_defWidth;
v___x_445_ = l_Std_Format_pretty(v_a_443_, v___x_444_, v___x_387_, v___x_387_);
v_value_390_ = v___x_445_;
goto v___jp_389_;
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec_ref(v_bs_x27_388_);
lean_dec(v_fst_385_);
v_a_446_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_442_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_442_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec_ref(v_bs_x27_388_);
lean_dec(v_fst_385_);
v_a_454_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_439_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_439_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
v___jp_462_:
{
lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_traceState_471_; lean_object* v_recordedDeps_472_; lean_object* v_messages_473_; lean_object* v_infoState_474_; lean_object* v_snapshotTasks_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_485_; 
v___x_466_ = lean_st_ref_take(v___y_380_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
v_nextMacroScope_468_ = lean_ctor_get(v___x_466_, 1);
v_ngen_469_ = lean_ctor_get(v___x_466_, 2);
v_auxDeclNGen_470_ = lean_ctor_get(v___x_466_, 3);
v_traceState_471_ = lean_ctor_get(v___x_466_, 4);
v_recordedDeps_472_ = lean_ctor_get(v___x_466_, 6);
v_messages_473_ = lean_ctor_get(v___x_466_, 7);
v_infoState_474_ = lean_ctor_get(v___x_466_, 8);
v_snapshotTasks_475_ = lean_ctor_get(v___x_466_, 9);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___x_466_, 5);
lean_dec(v_unused_486_);
v___x_477_ = v___x_466_;
v_isShared_478_ = v_isSharedCheck_485_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_snapshotTasks_475_);
lean_inc(v_infoState_474_);
lean_inc(v_messages_473_);
lean_inc(v_recordedDeps_472_);
lean_inc(v_traceState_471_);
lean_inc(v_auxDeclNGen_470_);
lean_inc(v_ngen_469_);
lean_inc(v_nextMacroScope_468_);
lean_inc(v_env_467_);
lean_dec(v___x_466_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_485_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_479_ = l_Lean_Kernel_enableDiag(v_env_467_, v___y_465_);
v___x_480_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 5, v___x_480_);
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_nextMacroScope_468_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_ngen_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v_reuseFailAlloc_484_, 4, v_traceState_471_);
lean_ctor_set(v_reuseFailAlloc_484_, 5, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_484_, 6, v_recordedDeps_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 7, v_messages_473_);
lean_ctor_set(v_reuseFailAlloc_484_, 8, v_infoState_474_);
lean_ctor_set(v_reuseFailAlloc_484_, 9, v_snapshotTasks_475_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_st_ref_put(v___y_380_, v___x_482_);
lean_inc_ref(v_inheritedTraceOptions_415_);
lean_inc(v_cancelTk_x3f_414_);
lean_inc(v_currMacroScope_413_);
lean_inc(v_quotContext_412_);
lean_inc(v_maxHeartbeats_411_);
lean_inc(v_initHeartbeats_410_);
lean_inc(v_openDecls_409_);
lean_inc(v_currNamespace_408_);
lean_inc_ref(v_fileMap_406_);
lean_inc_ref(v_fileName_405_);
v___y_418_ = v___y_463_;
v___y_419_ = v___y_464_;
v_fileName_420_ = v_fileName_405_;
v_fileMap_421_ = v_fileMap_406_;
v_currNamespace_422_ = v_currNamespace_408_;
v_openDecls_423_ = v_openDecls_409_;
v_initHeartbeats_424_ = v_initHeartbeats_410_;
v_maxHeartbeats_425_ = v_maxHeartbeats_411_;
v_quotContext_426_ = v_quotContext_412_;
v_currMacroScope_427_ = v_currMacroScope_413_;
v_cancelTk_x3f_428_ = v_cancelTk_x3f_414_;
v_inheritedTraceOptions_429_ = v_inheritedTraceOptions_415_;
v_currRecDepth_430_ = v_currRecDepth_401_;
v_ref_431_ = v_ref_402_;
v_suppressElabErrors_432_ = v_suppressElabErrors_403_;
v_isRecordingDeps_433_ = v_isRecordingDeps_404_;
v___y_434_ = v___y_380_;
goto v___jp_417_;
}
}
}
v___jp_487_:
{
if (v___y_491_ == 0)
{
v___y_463_ = v___y_488_;
v___y_464_ = v___y_489_;
v___y_465_ = v___y_490_;
goto v___jp_462_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_415_);
lean_inc(v_cancelTk_x3f_414_);
lean_inc(v_currMacroScope_413_);
lean_inc(v_quotContext_412_);
lean_inc(v_maxHeartbeats_411_);
lean_inc(v_initHeartbeats_410_);
lean_inc(v_openDecls_409_);
lean_inc(v_currNamespace_408_);
lean_inc_ref(v_fileMap_406_);
lean_inc_ref(v_fileName_405_);
v___y_418_ = v___y_488_;
v___y_419_ = v___y_489_;
v_fileName_420_ = v_fileName_405_;
v_fileMap_421_ = v_fileMap_406_;
v_currNamespace_422_ = v_currNamespace_408_;
v_openDecls_423_ = v_openDecls_409_;
v_initHeartbeats_424_ = v_initHeartbeats_410_;
v_maxHeartbeats_425_ = v_maxHeartbeats_411_;
v_quotContext_426_ = v_quotContext_412_;
v_currMacroScope_427_ = v_currMacroScope_413_;
v_cancelTk_x3f_428_ = v_cancelTk_x3f_414_;
v_inheritedTraceOptions_429_ = v_inheritedTraceOptions_415_;
v_currRecDepth_430_ = v_currRecDepth_401_;
v_ref_431_ = v_ref_402_;
v_suppressElabErrors_432_ = v_suppressElabErrors_403_;
v_isRecordingDeps_433_ = v_isRecordingDeps_404_;
v___y_434_ = v___y_380_;
goto v___jp_417_;
}
}
v___jp_492_:
{
if (v___y_495_ == 0)
{
v___y_488_ = v___y_493_;
v___y_489_ = v___y_494_;
v___y_490_ = v___y_496_;
v___y_491_ = v___x_382_;
goto v___jp_487_;
}
else
{
v___y_463_ = v___y_493_;
v___y_464_ = v___y_494_;
v___y_465_ = v___y_496_;
goto v___jp_462_;
}
}
v___jp_497_:
{
uint16_t v___x_499_; lean_object* v___x_500_; lean_object* v_env_501_; uint8_t v___x_502_; uint16_t v___x_503_; uint16_t v___x_504_; uint16_t v___x_505_; uint8_t v___x_506_; 
v___x_499_ = l_Lean_OptionFlags_ofOptions(v___y_498_);
v___x_500_ = lean_st_ref_get(v___y_380_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_env_501_);
lean_dec(v___x_500_);
v___x_502_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_501_);
lean_dec_ref(v_env_501_);
v___x_503_ = 512;
v___x_504_ = lean_uint16_land(v___x_499_, v___x_503_);
v___x_505_ = 0;
v___x_506_ = lean_uint16_dec_eq(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
if (v___x_382_ == 0)
{
v___y_493_ = v___x_499_;
v___y_494_ = v___y_498_;
v___y_495_ = v___x_502_;
v___y_496_ = v___x_382_;
goto v___jp_492_;
}
else
{
v___y_488_ = v___x_499_;
v___y_489_ = v___y_498_;
v___y_490_ = v___x_382_;
v___y_491_ = v___x_502_;
goto v___jp_487_;
}
}
else
{
uint8_t v___x_507_; 
v___x_507_ = 0;
v___y_493_ = v___x_499_;
v___y_494_ = v___y_498_;
v___y_495_ = v___x_502_;
v___y_496_ = v___x_507_;
goto v___jp_492_;
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec(v_snd_386_);
v___x_511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6));
v_value_390_ = v___x_511_;
goto v___jp_389_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; 
v___x_391_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_385_, v___x_382_);
v___x_392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__0));
v___x_393_ = lean_string_append(v___x_391_, v___x_392_);
v___x_394_ = lean_string_append(v___x_393_, v_value_390_);
lean_dec_ref(v_value_390_);
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_375_, v___x_395_);
v___x_397_ = lean_array_uset(v_bs_x27_388_, v_i_375_, v___x_394_);
v_i_375_ = v___x_396_;
v_bs_376_ = v___x_397_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_374_ = stack[0].m_num;
size_t v_i_375_ = stack[1].m_num;
lean_object* v_bs_376_ = stack[2].m_obj;
lean_object* v___y_377_ = stack[3].m_obj;
lean_object* v___y_378_ = stack[4].m_obj;
lean_object* v___y_379_ = stack[5].m_obj;
lean_object* v___y_380_ = stack[6].m_obj;
lean_object* v_res_512_;
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_374_, v_i_375_, v_bs_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_522_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_boxed_521_, v_i_boxed_522_, v_bs_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object* v_s_524_, lean_object* v_pos_525_){
_start:
{
lean_object* v_str_526_; lean_object* v_startInclusive_527_; lean_object* v_endExclusive_528_; lean_object* v___x_529_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v_decide_540_; 
v_str_526_ = lean_ctor_get(v_s_524_, 0);
v_startInclusive_527_ = lean_ctor_get(v_s_524_, 1);
v_endExclusive_528_ = lean_ctor_get(v_s_524_, 2);
v___x_529_ = lean_nat_add(v_startInclusive_527_, v_pos_525_);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_sub(v_endExclusive_528_, v___x_529_);
v_decide_540_ = lean_nat_dec_eq(v___x_538_, v___x_539_);
lean_dec(v___x_539_);
if (v_decide_540_ == 0)
{
uint32_t v___x_541_; uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_541_ = lean_string_utf8_get_fast(v_str_526_, v___x_529_);
v___x_542_ = 32;
v___x_543_ = lean_uint32_dec_eq(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
uint32_t v___x_544_; uint8_t v___x_545_; 
v___x_544_ = 9;
v___x_545_ = lean_uint32_dec_eq(v___x_541_, v___x_544_);
if (v___x_545_ == 0)
{
uint32_t v___x_546_; uint8_t v___x_547_; 
v___x_546_ = 13;
v___x_547_ = lean_uint32_dec_eq(v___x_541_, v___x_546_);
if (v___x_547_ == 0)
{
uint32_t v___x_548_; uint8_t v___x_549_; 
v___x_548_ = 10;
v___x_549_ = lean_uint32_dec_eq(v___x_541_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v___x_529_);
return v_pos_525_;
}
else
{
goto v___jp_530_;
}
}
else
{
goto v___jp_530_;
}
}
else
{
goto v___jp_530_;
}
}
else
{
goto v___jp_530_;
}
}
else
{
lean_dec(v___x_529_);
return v_pos_525_;
}
v___jp_530_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_531_ = lean_string_utf8_next_fast(v_str_526_, v___x_529_);
v___x_532_ = lean_nat_sub(v___x_531_, v___x_529_);
lean_dec(v___x_529_);
v___x_533_ = lean_nat_add(v_pos_525_, v___x_532_);
lean_dec(v___x_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_pos_525_, v___x_534_);
v___x_536_ = lean_nat_dec_le(v___x_535_, v___x_533_);
lean_dec(v___x_535_);
if (v___x_536_ == 0)
{
lean_dec(v___x_533_);
return v_pos_525_;
}
else
{
lean_dec(v_pos_525_);
v_pos_525_ = v___x_533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object* v_s_550_, lean_object* v_pos_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v_s_550_, v_pos_551_);
lean_dec_ref(v_s_550_);
return v_res_552_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2));
v___x_558_ = l_Lean_stringToMessageData(v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_565_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8));
v___x_566_ = lean_unsigned_to_nat(14u);
v___x_567_ = lean_unsigned_to_nat(22u);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7));
v___x_569_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6));
v___x_570_ = l_mkPanicMessageWithDecl(v___x_569_, v___x_568_, v___x_567_, v___x_566_, v___x_565_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1(void){
_start:
{
uint32_t v___x_571_; lean_object* v___x_572_; 
v___x_571_ = 32;
v___x_572_ = lean_box_uint32(v___x_571_);
return v___x_572_;
}
}
lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(lean_object* v_fields_573_, lean_object* v_stx_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc(v_stx_574_);
v___x_580_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(v_stx_574_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_802_; 
v_val_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_802_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_802_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_802_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
size_t v_sz_585_; size_t v___x_586_; lean_object* v___x_587_; 
v_sz_585_ = lean_array_size(v_fields_573_);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_585_, v___x_586_, v_fields_573_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_793_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_574_, v_val_581_, v_a_577_);
lean_dec(v_stx_574_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_793_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_793_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_793_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_594_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_679_; lean_object* v___y_680_; uint8_t v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; uint8_t v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; uint8_t v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v_startInclusive_701_; lean_object* v_endExclusive_702_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; uint8_t v___y_720_; uint8_t v___y_721_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_764_; lean_object* v___y_777_; uint8_t v___x_780_; 
v___x_594_ = 1;
v___x_780_ = lean_unbox(v_a_590_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_781_ = lean_array_to_list(v_a_588_);
v___x_782_ = lean_box(1);
v___x_783_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(v___x_781_, v___x_782_);
v___y_764_ = v___x_783_;
goto v___jp_763_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_784_ = lean_box(0);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_array_get_size(v_a_588_);
v___x_787_ = lean_nat_dec_lt(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_dec(v_a_588_);
v___y_777_ = v___x_784_;
goto v___jp_776_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = lean_nat_dec_le(v___x_786_, v___x_786_);
if (v___x_788_ == 0)
{
if (v___x_787_ == 0)
{
lean_dec(v_a_588_);
v___y_777_ = v___x_784_;
goto v___jp_776_;
}
else
{
size_t v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_usize_of_nat(v___x_786_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_588_, v___x_586_, v___x_789_, v___x_784_);
lean_dec(v_a_588_);
v___y_777_ = v___x_790_;
goto v___jp_776_;
}
}
else
{
size_t v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_usize_of_nat(v___x_786_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_588_, v___x_586_, v___x_791_, v___x_784_);
lean_dec(v_a_588_);
v___y_777_ = v___x_792_;
goto v___jp_776_;
}
}
}
v___jp_595_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_600_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_577_);
v___x_601_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_602_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v___x_600_, v___x_601_);
lean_dec_ref(v___x_600_);
lean_inc(v___y_599_);
v___x_603_ = lean_apply_1(v___y_598_, v___y_599_);
v___x_604_ = l_Std_Format_pretty(v___y_597_, v___x_602_, v___y_596_, v___x_603_);
lean_dec(v___x_602_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 1);
lean_ctor_set(v___x_592_, 0, v___x_604_);
v___x_606_ = v___x_592_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_623_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_607_ = lean_box(0);
v___x_608_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1));
v___x_609_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_607_);
lean_ctor_set(v___x_609_, 3, v___x_607_);
lean_ctor_set(v___x_609_, 4, v___x_607_);
lean_ctor_set(v___x_609_, 5, v___x_608_);
lean_inc(v___y_599_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___y_599_);
lean_ctor_set(v___x_610_, 1, v___y_599_);
v___x_611_ = l_Lean_Syntax_ofRange(v___x_610_, v___x_594_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_611_);
v___x_613_ = v___x_583_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_622_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; lean_object* v___x_621_; 
v___x_614_ = 0;
v___x_615_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_607_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3, v___x_614_);
v___x_616_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_mk_empty_array_with_capacity(v___x_617_);
v___x_619_ = lean_array_push(v___x_618_, v___x_615_);
v___x_620_ = 0;
v___x_621_ = l_Lean_MessageData_hint(v___x_616_, v___x_619_, v___x_607_, v___x_607_, v___x_620_, v_a_577_, v_a_578_);
lean_dec_ref(v___x_619_);
return v___x_621_;
}
}
}
v___jp_624_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v_fst_631_);
lean_ctor_set(v___x_633_, 1, v___y_625_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_snd_632_);
if (lean_obj_tag(v___y_629_) == 0)
{
if (lean_obj_tag(v___y_627_) == 0)
{
v___y_596_ = v___y_626_;
v___y_597_ = v___x_634_;
v___y_598_ = v___y_630_;
v___y_599_ = v___y_628_;
goto v___jp_595_;
}
else
{
lean_object* v_val_635_; 
lean_dec(v___y_628_);
v_val_635_ = lean_ctor_get(v___y_627_, 0);
lean_inc(v_val_635_);
lean_dec_ref_known(v___y_627_, 1);
v___y_596_ = v___y_626_;
v___y_597_ = v___x_634_;
v___y_598_ = v___y_630_;
v___y_599_ = v_val_635_;
goto v___jp_595_;
}
}
else
{
lean_object* v_val_636_; 
lean_dec(v___y_628_);
lean_dec(v___y_627_);
v_val_636_ = lean_ctor_get(v___y_629_, 0);
lean_inc(v_val_636_);
lean_dec_ref_known(v___y_629_, 1);
v___y_596_ = v___y_626_;
v___y_597_ = v___x_634_;
v___y_598_ = v___y_630_;
v___y_599_ = v_val_636_;
goto v___jp_595_;
}
}
v___jp_637_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_box(1);
v___x_645_ = lean_box(0);
v___y_625_ = v___y_638_;
v___y_626_ = v___y_639_;
v___y_627_ = v___y_640_;
v___y_628_ = v___y_642_;
v___y_629_ = v___y_641_;
v___y_630_ = v___y_643_;
v_fst_631_ = v___x_644_;
v_snd_632_ = v___x_645_;
goto v___jp_624_;
}
v___jp_646_:
{
if (lean_obj_tag(v___y_649_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_box(1);
v___x_654_ = lean_box(0);
v___y_625_ = v___y_647_;
v___y_626_ = v___y_648_;
v___y_627_ = v___y_649_;
v___y_628_ = v___y_651_;
v___y_629_ = v___y_650_;
v___y_630_ = v___y_652_;
v_fst_631_ = v___x_653_;
v_snd_632_ = v___x_654_;
goto v___jp_624_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_val_655_ = lean_ctor_get(v___y_649_, 0);
lean_inc_ref(v___y_652_);
lean_inc(v_val_655_);
v___x_656_ = lean_apply_1(v___y_652_, v_val_655_);
v___x_657_ = lean_nat_sub(v___y_648_, v___x_656_);
lean_dec(v___x_656_);
v___x_658_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
v___x_659_ = l_List_replicateTR___redArg(v___x_657_, v___x_658_);
v___x_660_ = lean_string_mk(v___x_659_);
v___x_661_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
v___x_662_ = lean_box(0);
v___y_625_ = v___y_647_;
v___y_626_ = v___y_648_;
v___y_627_ = v___y_649_;
v___y_628_ = v___y_651_;
v___y_629_ = v___y_650_;
v___y_630_ = v___y_652_;
v_fst_631_ = v___x_661_;
v_snd_632_ = v___x_662_;
goto v___jp_624_;
}
}
v___jp_663_:
{
uint8_t v___x_673_; 
v___x_673_ = lean_unbox(v_a_590_);
lean_dec(v_a_590_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_lt(v___x_674_, v___y_670_);
lean_dec(v___y_670_);
if (v___x_675_ == 0)
{
if (v___y_665_ == 0)
{
if (v___y_671_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5));
v___y_625_ = v___y_664_;
v___y_626_ = v___y_666_;
v___y_627_ = v___y_672_;
v___y_628_ = v___y_668_;
v___y_629_ = v___y_667_;
v___y_630_ = v___y_669_;
v_fst_631_ = v___x_676_;
v_snd_632_ = v___x_676_;
goto v___jp_624_;
}
else
{
v___y_647_ = v___y_664_;
v___y_648_ = v___y_666_;
v___y_649_ = v___y_672_;
v___y_650_ = v___y_667_;
v___y_651_ = v___y_668_;
v___y_652_ = v___y_669_;
goto v___jp_646_;
}
}
else
{
if (v___y_671_ == 0)
{
v___y_638_ = v___y_664_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_672_;
v___y_641_ = v___y_667_;
v___y_642_ = v___y_668_;
v___y_643_ = v___y_669_;
goto v___jp_637_;
}
else
{
v___y_647_ = v___y_664_;
v___y_648_ = v___y_666_;
v___y_649_ = v___y_672_;
v___y_650_ = v___y_667_;
v___y_651_ = v___y_668_;
v___y_652_ = v___y_669_;
goto v___jp_646_;
}
}
}
else
{
v___y_638_ = v___y_664_;
v___y_639_ = v___y_666_;
v___y_640_ = v___y_672_;
v___y_641_ = v___y_667_;
v___y_642_ = v___y_668_;
v___y_643_ = v___y_669_;
goto v___jp_637_;
}
}
else
{
lean_object* v___x_677_; 
lean_dec(v___y_670_);
v___x_677_ = lean_box(0);
v___y_625_ = v___y_664_;
v___y_626_ = v___y_666_;
v___y_627_ = v___y_672_;
v___y_628_ = v___y_668_;
v___y_629_ = v___y_667_;
v___y_630_ = v___y_669_;
v_fst_631_ = v___x_677_;
v_snd_632_ = v___x_677_;
goto v___jp_624_;
}
}
v___jp_678_:
{
lean_object* v___x_688_; 
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v___y_687_);
v___y_664_ = v___y_679_;
v___y_665_ = v___y_681_;
v___y_666_ = v___y_680_;
v___y_667_ = v___y_683_;
v___y_668_ = v___y_682_;
v___y_669_ = v___y_684_;
v___y_670_ = v___y_686_;
v___y_671_ = v___y_685_;
v___y_672_ = v___x_688_;
goto v___jp_663_;
}
v___jp_689_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v_decide_706_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___y_700_, v___x_703_);
lean_dec_ref(v___y_700_);
v___x_705_ = lean_nat_sub(v_endExclusive_702_, v_startInclusive_701_);
lean_dec(v_startInclusive_701_);
lean_dec(v_endExclusive_702_);
v_decide_706_ = lean_nat_dec_eq(v___x_704_, v___x_705_);
lean_dec(v___x_705_);
lean_dec(v___x_704_);
if (v_decide_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec(v___y_692_);
lean_dec(v___y_691_);
v___x_707_ = lean_box(0);
v___y_664_ = v___y_690_;
v___y_665_ = v___y_694_;
v___y_666_ = v___y_693_;
v___y_667_ = v___y_696_;
v___y_668_ = v___y_695_;
v___y_669_ = v___y_697_;
v___y_670_ = v___y_699_;
v___y_671_ = v___y_698_;
v___y_672_ = v___x_707_;
goto v___jp_663_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_le(v___y_691_, v___y_692_);
if (v___x_708_ == 0)
{
lean_dec(v___y_691_);
v___y_679_ = v___y_690_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_695_;
v___y_683_ = v___y_696_;
v___y_684_ = v___y_697_;
v___y_685_ = v___y_698_;
v___y_686_ = v___y_699_;
v___y_687_ = v___y_692_;
goto v___jp_678_;
}
else
{
lean_dec(v___y_692_);
v___y_679_ = v___y_690_;
v___y_680_ = v___y_693_;
v___y_681_ = v___y_694_;
v___y_682_ = v___y_695_;
v___y_683_ = v___y_696_;
v___y_684_ = v___y_697_;
v___y_685_ = v___y_698_;
v___y_686_ = v___y_699_;
v___y_687_ = v___y_691_;
goto v___jp_678_;
}
}
}
v___jp_709_:
{
if (v___y_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_startInclusive_724_; lean_object* v_endExclusive_725_; 
lean_dec_ref(v___y_712_);
v___x_722_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9);
v___x_723_ = l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___x_722_);
v_startInclusive_724_ = lean_ctor_get(v___x_723_, 1);
lean_inc(v_startInclusive_724_);
v_endExclusive_725_ = lean_ctor_get(v___x_723_, 2);
lean_inc(v_endExclusive_725_);
v___y_690_ = v___y_710_;
v___y_691_ = v___y_711_;
v___y_692_ = v___y_715_;
v___y_693_ = v___y_714_;
v___y_694_ = v___y_713_;
v___y_695_ = v___y_717_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_718_;
v___y_698_ = v___y_720_;
v___y_699_ = v___y_719_;
v___y_700_ = v___x_723_;
v_startInclusive_701_ = v_startInclusive_724_;
v_endExclusive_702_ = v_endExclusive_725_;
goto v___jp_689_;
}
else
{
lean_object* v___x_726_; 
lean_inc_n(v___y_715_, 2);
lean_inc_n(v___y_717_, 2);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___y_712_);
lean_ctor_set(v___x_726_, 1, v___y_717_);
lean_ctor_set(v___x_726_, 2, v___y_715_);
v___y_690_ = v___y_710_;
v___y_691_ = v___y_711_;
v___y_692_ = v___y_715_;
v___y_693_ = v___y_714_;
v___y_694_ = v___y_713_;
v___y_695_ = v___y_717_;
v___y_696_ = v___y_716_;
v___y_697_ = v___y_718_;
v___y_698_ = v___y_720_;
v___y_699_ = v___y_719_;
v___y_700_ = v___x_726_;
v_startInclusive_701_ = v___y_717_;
v_endExclusive_702_ = v___y_715_;
goto v___jp_689_;
}
}
v___jp_727_:
{
lean_object* v_lastFieldTailPos_x3f_732_; uint8_t v_hasWith_733_; lean_object* v_numFields_734_; lean_object* v_leaderPos_735_; lean_object* v_leaderTailPos_736_; lean_object* v_closingPos_737_; lean_object* v___x_738_; lean_object* v_line_739_; lean_object* v___x_740_; lean_object* v_line_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_lastFieldTailPos_x3f_732_ = lean_ctor_get(v_val_581_, 1);
lean_inc(v_lastFieldTailPos_x3f_732_);
v_hasWith_733_ = lean_ctor_get_uint8(v_val_581_, sizeof(void*)*7);
v_numFields_734_ = lean_ctor_get(v_val_581_, 2);
lean_inc(v_numFields_734_);
v_leaderPos_735_ = lean_ctor_get(v_val_581_, 4);
lean_inc(v_leaderPos_735_);
v_leaderTailPos_736_ = lean_ctor_get(v_val_581_, 5);
lean_inc(v_leaderTailPos_736_);
v_closingPos_737_ = lean_ctor_get(v_val_581_, 6);
lean_inc(v_closingPos_737_);
lean_dec(v_val_581_);
lean_inc_ref_n(v___y_729_, 2);
v___x_738_ = l_Lean_FileMap_utf8PosToLspPos(v___y_729_, v_leaderPos_735_);
lean_dec(v_leaderPos_735_);
v_line_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_line_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Lean_FileMap_utf8PosToLspPos(v___y_729_, v_closingPos_737_);
lean_dec(v_closingPos_737_);
v_line_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_line_741_);
lean_dec_ref(v___x_740_);
v___x_742_ = lean_nat_dec_lt(v_line_739_, v_line_741_);
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_line_739_, v___x_743_);
lean_dec(v_line_739_);
v___x_745_ = lean_nat_dec_le(v_line_741_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v_line_741_);
if (v___x_745_ == 0)
{
lean_object* v_source_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_source_746_ = lean_ctor_get(v___y_729_, 0);
lean_inc_ref_n(v_source_746_, 3);
lean_dec_ref(v___y_729_);
v___x_747_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_746_, v_leaderTailPos_736_);
v___x_748_ = lean_nat_add(v___y_731_, v___x_743_);
lean_inc(v___x_747_);
v___x_749_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v_source_746_, v___x_748_, v___x_747_);
v___x_750_ = lean_string_utf8_next(v_source_746_, v___x_747_);
lean_dec(v___x_747_);
v___x_751_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_746_, v___x_750_);
lean_dec(v___x_750_);
v___x_752_ = lean_string_is_valid_pos(v_source_746_, v_leaderTailPos_736_);
if (v___x_752_ == 0)
{
v___y_710_ = v___y_728_;
v___y_711_ = v___x_749_;
v___y_712_ = v_source_746_;
v___y_713_ = v_hasWith_733_;
v___y_714_ = v___y_731_;
v___y_715_ = v___x_751_;
v___y_716_ = v_lastFieldTailPos_x3f_732_;
v___y_717_ = v_leaderTailPos_736_;
v___y_718_ = v___y_730_;
v___y_719_ = v_numFields_734_;
v___y_720_ = v___x_742_;
v___y_721_ = v___x_752_;
goto v___jp_709_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = lean_string_is_valid_pos(v_source_746_, v___x_751_);
if (v___x_753_ == 0)
{
v___y_710_ = v___y_728_;
v___y_711_ = v___x_749_;
v___y_712_ = v_source_746_;
v___y_713_ = v_hasWith_733_;
v___y_714_ = v___y_731_;
v___y_715_ = v___x_751_;
v___y_716_ = v_lastFieldTailPos_x3f_732_;
v___y_717_ = v_leaderTailPos_736_;
v___y_718_ = v___y_730_;
v___y_719_ = v_numFields_734_;
v___y_720_ = v___x_742_;
v___y_721_ = v___x_753_;
goto v___jp_709_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = lean_nat_dec_le(v_leaderTailPos_736_, v___x_751_);
v___y_710_ = v___y_728_;
v___y_711_ = v___x_749_;
v___y_712_ = v_source_746_;
v___y_713_ = v_hasWith_733_;
v___y_714_ = v___y_731_;
v___y_715_ = v___x_751_;
v___y_716_ = v_lastFieldTailPos_x3f_732_;
v___y_717_ = v_leaderTailPos_736_;
v___y_718_ = v___y_730_;
v___y_719_ = v_numFields_734_;
v___y_720_ = v___x_742_;
v___y_721_ = v___x_754_;
goto v___jp_709_;
}
}
}
else
{
lean_object* v___x_755_; 
lean_dec_ref(v___y_729_);
v___x_755_ = lean_box(0);
v___y_664_ = v___y_728_;
v___y_665_ = v_hasWith_733_;
v___y_666_ = v___y_731_;
v___y_667_ = v_lastFieldTailPos_x3f_732_;
v___y_668_ = v_leaderTailPos_736_;
v___y_669_ = v___y_730_;
v___y_670_ = v_numFields_734_;
v___y_671_ = v___x_742_;
v___y_672_ = v___x_755_;
goto v___jp_663_;
}
}
v___jp_756_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(2u);
v___x_762_ = lean_nat_add(v___y_760_, v___x_761_);
lean_dec(v___y_760_);
v___y_728_ = v___y_757_;
v___y_729_ = v___y_758_;
v___y_730_ = v___y_759_;
v___y_731_ = v___x_762_;
goto v___jp_727_;
}
v___jp_763_:
{
lean_object* v_toCold_765_; lean_object* v_fileMap_766_; lean_object* v_initFieldPos_x3f_767_; lean_object* v_openingPos_768_; lean_object* v_closingPos_769_; lean_object* v___f_770_; 
v_toCold_765_ = lean_ctor_get(v_a_577_, 0);
v_fileMap_766_ = lean_ctor_get(v_toCold_765_, 1);
v_initFieldPos_x3f_767_ = lean_ctor_get(v_val_581_, 0);
v_openingPos_768_ = lean_ctor_get(v_val_581_, 3);
v_closingPos_769_ = lean_ctor_get(v_val_581_, 6);
lean_inc_ref(v_fileMap_766_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed), 2, 1);
lean_closure_set(v___f_770_, 0, v_fileMap_766_);
if (lean_obj_tag(v_initFieldPos_x3f_767_) == 1)
{
lean_object* v_val_771_; lean_object* v___x_772_; 
v_val_771_ = lean_ctor_get(v_initFieldPos_x3f_767_, 0);
lean_inc_ref_n(v_fileMap_766_, 2);
v___x_772_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_766_, v_val_771_);
v___y_728_ = v___y_764_;
v___y_729_ = v_fileMap_766_;
v___y_730_ = v___f_770_;
v___y_731_ = v___x_772_;
goto v___jp_727_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
lean_inc_ref_n(v_fileMap_766_, 2);
v___x_773_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_766_, v_openingPos_768_);
v___x_774_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_766_, v_closingPos_769_);
v___x_775_ = lean_nat_dec_le(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_dec(v___x_773_);
lean_inc_ref(v_fileMap_766_);
v___y_757_ = v___y_764_;
v___y_758_ = v_fileMap_766_;
v___y_759_ = v___f_770_;
v___y_760_ = v___x_774_;
goto v___jp_756_;
}
else
{
lean_dec(v___x_774_);
lean_inc_ref(v_fileMap_766_);
v___y_757_ = v___y_764_;
v___y_758_ = v_fileMap_766_;
v___y_759_ = v___f_770_;
v___y_760_ = v___x_773_;
goto v___jp_756_;
}
}
}
v___jp_776_:
{
uint8_t v___x_778_; lean_object* v___x_779_; 
v___x_778_ = 1;
v___x_779_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_779_, 0, v___y_777_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*1, v___x_778_);
v___y_764_ = v___x_779_;
goto v___jp_763_;
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_del_object(v___x_583_);
lean_dec(v_val_581_);
lean_dec(v_stx_574_);
v_a_794_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_587_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_587_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec(v___x_580_);
lean_dec(v_stx_574_);
lean_dec_ref(v_fields_573_);
v___x_803_ = l_Lean_MessageData_nil;
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_StructInst_mkMissingFieldsHint_0interp(lean_interpreter_value* stack)
{
lean_object* v_fields_573_ = stack[0].m_obj;
lean_object* v_stx_574_ = stack[1].m_obj;
lean_object* v_a_575_ = stack[2].m_obj;
lean_object* v_a_576_ = stack[3].m_obj;
lean_object* v_a_577_ = stack[4].m_obj;
lean_object* v_a_578_ = stack[5].m_obj;
lean_object* v_res_805_;
v_res_805_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_573_, v_stx_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
stack->m_obj
 = v_res_805_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object* v_fields_806_, lean_object* v_stx_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_806_, v_stx_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(lean_object* v___x_814_, lean_object* v_n_815_, lean_object* v_j_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v___x_814_, v_j_816_, v_a_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object* v___x_820_, lean_object* v_n_821_, lean_object* v_j_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v___x_820_, v_n_821_, v_j_822_, v_a_823_, v_a_824_);
lean_dec(v_n_821_);
lean_dec_ref(v___x_820_);
return v_res_825_;
}
}
lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_StructInstHint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1 = _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_StructInstHint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_StructInstHint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_StructInstHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_StructInstHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_StructInstHint(builtin);
}
#ifdef __cplusplus
}
#endif
