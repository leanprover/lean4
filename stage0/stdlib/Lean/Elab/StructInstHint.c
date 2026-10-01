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
uint8_t v___y_12_; lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; uint8_t v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; uint8_t v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v_fst_39_; uint8_t v_snd_40_; lean_object* v___x_67_; 
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
lean_ctor_set(v___x_20_, 0, v___y_18_);
lean_ctor_set(v___x_20_, 1, v___y_19_);
lean_ctor_set(v___x_20_, 2, v___y_15_);
lean_ctor_set(v___x_20_, 3, v___y_14_);
lean_ctor_set(v___x_20_, 4, v___y_16_);
lean_ctor_set(v___x_20_, 5, v___y_13_);
lean_ctor_set(v___x_20_, 6, v___y_17_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*7, v___y_12_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
v___jp_22_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_31_ = lean_array_get_size(v___y_29_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v___x_31_, v___x_32_);
v___x_34_ = lean_nat_dec_lt(v___x_33_, v___x_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___x_33_);
lean_dec_ref(v___y_29_);
v___x_35_ = lean_box(0);
v___y_12_ = v___y_23_;
v___y_13_ = v___y_25_;
v___y_14_ = v___y_24_;
v___y_15_ = v___x_31_;
v___y_16_ = v___y_26_;
v___y_17_ = v___y_28_;
v___y_18_ = v___y_30_;
v___y_19_ = v___x_35_;
goto v___jp_11_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_fget(v___y_29_, v___x_33_);
lean_dec(v___x_33_);
lean_dec_ref(v___y_29_);
v___x_37_ = l_Lean_Syntax_getTailPos_x3f(v___x_36_, v___y_27_);
lean_dec(v___x_36_);
v___y_12_ = v___y_23_;
v___y_13_ = v___y_25_;
v___y_14_ = v___y_24_;
v___y_15_ = v___x_31_;
v___y_16_ = v___y_26_;
v___y_17_ = v___y_28_;
v___y_18_ = v___y_30_;
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
v___y_23_ = v_snd_40_;
v___y_24_ = v_val_52_;
v___y_25_ = v_val_47_;
v___y_26_ = v_val_44_;
v___y_27_ = v___x_41_;
v___y_28_ = v_val_57_;
v___y_29_ = v___x_61_;
v___y_30_ = v___x_64_;
goto v___jp_22_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_array_fget_borrowed(v___x_61_, v___x_48_);
v___x_66_ = l_Lean_Syntax_getPos_x3f(v___x_65_, v___x_41_);
v___y_23_ = v_snd_40_;
v___y_24_ = v_val_52_;
v___y_25_ = v_val_47_;
v___y_26_ = v_val_44_;
v___y_27_ = v___x_41_;
v___y_28_ = v_val_57_;
v___y_29_ = v___x_61_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(lean_object* v_stx_139_, lean_object* v_view_140_, lean_object* v_a_141_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___boxed(lean_object* v_stx_214_, lean_object* v_view_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_214_, v_view_215_, v_a_216_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_view_215_);
lean_dec(v_stx_214_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(lean_object* v_stx_219_, lean_object* v_view_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_219_, v_view_220_, v_a_223_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___boxed(lean_object* v_stx_227_, lean_object* v_view_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(v_stx_227_, v_view_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec_ref(v_view_228_);
lean_dec(v_stx_227_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
lean_object* v_name_237_; lean_object* v_defValue_238_; lean_object* v_map_239_; lean_object* v___x_240_; 
v_name_237_ = lean_ctor_get(v_opt_236_, 0);
v_defValue_238_ = lean_ctor_get(v_opt_236_, 1);
v_map_239_ = lean_ctor_get(v_opts_235_, 0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_239_, v_name_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_inc(v_defValue_238_);
return v_defValue_238_;
}
else
{
lean_object* v_val_241_; 
v_val_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_240_, 1);
if (lean_obj_tag(v_val_241_) == 3)
{
lean_object* v_v_242_; 
v_v_242_ = lean_ctor_get(v_val_241_, 0);
lean_inc(v_v_242_);
lean_dec_ref_known(v_val_241_, 1);
return v_v_242_;
}
else
{
lean_dec(v_val_241_);
lean_inc(v_defValue_238_);
return v_defValue_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object* v_opts_243_, lean_object* v_opt_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_opts_243_, v_opt_244_);
lean_dec_ref(v_opt_244_);
lean_dec_ref(v_opts_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object* v_msg_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = l_String_instInhabitedSlice;
v___x_248_ = lean_panic_fn_borrowed(v___x_247_, v_msg_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0));
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(v_x_252_);
lean_dec_ref(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object* v_fileMap_254_, lean_object* v_p_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_character_257_; 
v___x_256_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_254_, v_p_255_);
v_character_257_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_character_257_);
lean_dec_ref(v___x_256_);
return v_character_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object* v_fileMap_258_, lean_object* v_p_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_258_, v_p_259_);
lean_dec(v_p_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(lean_object* v___x_261_, lean_object* v_j_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_zero_264_; uint8_t v_isZero_265_; 
v_zero_264_ = lean_unsigned_to_nat(0u);
v_isZero_265_ = lean_nat_dec_eq(v_j_262_, v_zero_264_);
if (v_isZero_265_ == 1)
{
lean_dec(v_j_262_);
return v_a_263_;
}
else
{
lean_object* v_one_266_; lean_object* v_n_267_; lean_object* v___x_268_; 
v_one_266_ = lean_unsigned_to_nat(1u);
v_n_267_ = lean_nat_sub(v_j_262_, v_one_266_);
lean_dec(v_j_262_);
v___x_268_ = lean_string_utf8_next(v___x_261_, v_a_263_);
lean_dec(v_a_263_);
v_j_262_ = v_n_267_;
v_a_263_ = v___x_268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg___boxed(lean_object* v___x_270_, lean_object* v_j_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v___x_270_, v_j_271_, v_a_272_);
lean_dec_ref(v___x_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object* v_as_276_, size_t v_i_277_, size_t v_stop_278_, lean_object* v_b_279_){
_start:
{
uint8_t v___x_280_; 
v___x_280_ = lean_usize_dec_eq(v_i_277_, v_stop_278_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; size_t v___x_288_; size_t v___x_289_; 
v___x_281_ = lean_array_uget_borrowed(v_as_276_, v_i_277_);
v___x_282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___closed__0));
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v_b_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_box(1);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
lean_inc(v___x_281_);
v___x_286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_281_);
v___x_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_add(v_i_277_, v___x_288_);
v_i_277_ = v___x_289_;
v_b_279_ = v___x_287_;
goto _start;
}
else
{
return v_b_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7___boxed(lean_object* v_as_291_, lean_object* v_i_292_, lean_object* v_stop_293_, lean_object* v_b_294_){
_start:
{
size_t v_i_boxed_295_; size_t v_stop_boxed_296_; lean_object* v_res_297_; 
v_i_boxed_295_ = lean_unbox_usize(v_i_292_);
lean_dec(v_i_292_);
v_stop_boxed_296_ = lean_unbox_usize(v_stop_293_);
lean_dec(v_stop_293_);
v_res_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_as_291_, v_i_boxed_295_, v_stop_boxed_296_, v_b_294_);
lean_dec_ref(v_as_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6_spec__7(lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_dec(v_x_298_);
return v_x_299_;
}
else
{
lean_object* v_head_301_; lean_object* v_tail_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_312_; 
v_head_301_ = lean_ctor_get(v_x_300_, 0);
v_tail_302_ = lean_ctor_get(v_x_300_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_312_ == 0)
{
v___x_304_ = v_x_300_;
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_tail_302_);
lean_inc(v_head_301_);
lean_dec(v_x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_312_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
lean_inc(v_x_298_);
if (v_isShared_305_ == 0)
{
lean_ctor_set_tag(v___x_304_, 5);
lean_ctor_set(v___x_304_, 1, v_x_298_);
lean_ctor_set(v___x_304_, 0, v_x_299_);
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_x_299_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_x_298_);
v___x_307_ = v_reuseFailAlloc_311_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_308_, 0, v_head_301_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v_x_299_ = v___x_309_;
v_x_300_ = v_tail_302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v___x_315_; 
lean_dec(v_x_314_);
v___x_315_ = lean_box(0);
return v___x_315_;
}
else
{
lean_object* v_tail_316_; 
v_tail_316_ = lean_ctor_get(v_x_313_, 1);
if (lean_obj_tag(v_tail_316_) == 0)
{
lean_object* v_head_317_; lean_object* v___x_318_; 
lean_dec(v_x_314_);
v_head_317_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_head_317_);
lean_dec_ref_known(v_x_313_, 2);
v___x_318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_318_, 0, v_head_317_);
return v___x_318_;
}
else
{
lean_object* v_head_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
lean_inc(v_tail_316_);
v_head_319_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_head_319_);
lean_dec_ref_known(v_x_313_, 2);
v___x_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_320_, 0, v_head_319_);
v___x_321_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6_spec__7(v_x_314_, v___x_320_, v_tail_316_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(lean_object* v_o_325_, lean_object* v_k_326_, uint8_t v_v_327_){
_start:
{
lean_object* v_map_328_; uint8_t v_hasTrace_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_343_; 
v_map_328_ = lean_ctor_get(v_o_325_, 0);
v_hasTrace_329_ = lean_ctor_get_uint8(v_o_325_, sizeof(void*)*1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_o_325_);
if (v_isSharedCheck_343_ == 0)
{
v___x_331_ = v_o_325_;
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_map_328_);
lean_dec(v_o_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_343_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_333_, 0, v_v_327_);
lean_inc(v_k_326_);
v___x_334_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_326_, v___x_333_, v_map_328_);
if (v_hasTrace_329_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_338_; 
v___x_335_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___closed__1));
v___x_336_ = l_Lean_Name_isPrefixOf(v___x_335_, v_k_326_);
lean_dec(v_k_326_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_334_);
v___x_338_ = v___x_331_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_334_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_336_);
return v___x_338_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec(v_k_326_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_334_);
v___x_341_ = v___x_331_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_334_);
lean_ctor_set_uint8(v_reuseFailAlloc_342_, sizeof(void*)*1, v_hasTrace_329_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1___boxed(lean_object* v_o_344_, lean_object* v_k_345_, lean_object* v_v_346_){
_start:
{
uint8_t v_v_boxed_347_; lean_object* v_res_348_; 
v_v_boxed_347_ = lean_unbox(v_v_346_);
v_res_348_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(v_o_344_, v_k_345_, v_v_boxed_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object* v_opts_349_, lean_object* v_opt_350_, uint8_t v_val_351_){
_start:
{
lean_object* v_name_352_; lean_object* v___x_353_; 
v_name_352_ = lean_ctor_get(v_opt_350_, 0);
lean_inc(v_name_352_);
lean_dec_ref(v_opt_350_);
v___x_353_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1_spec__1(v_opts_349_, v_name_352_, v_val_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object* v_opts_354_, lean_object* v_opt_355_, lean_object* v_val_356_){
_start:
{
uint8_t v_val_boxed_357_; lean_object* v_res_358_; 
v_val_boxed_357_ = lean_unbox(v_val_356_);
v_res_358_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_354_, v_opt_355_, v_val_boxed_357_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3(void){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_363_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__3);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__4);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(size_t v_sz_369_, size_t v_i_370_, lean_object* v_bs_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_bs_371_);
return v___x_378_;
}
else
{
lean_object* v_v_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; lean_object* v_bs_x27_383_; lean_object* v_value_385_; 
v_v_379_ = lean_array_uget_borrowed(v_bs_371_, v_i_370_);
v_fst_380_ = lean_ctor_get(v_v_379_, 0);
lean_inc(v_fst_380_);
v_snd_381_ = lean_ctor_get(v_v_379_, 1);
lean_inc(v_snd_381_);
v___x_382_ = lean_unsigned_to_nat(0u);
v_bs_x27_383_ = lean_array_uset(v_bs_371_, v_i_370_, v___x_382_);
if (lean_obj_tag(v_snd_381_) == 1)
{
lean_object* v_toCold_394_; lean_object* v_val_395_; lean_object* v_currRecDepth_396_; lean_object* v_ref_397_; uint8_t v_suppressElabErrors_398_; uint8_t v_isRecordingDeps_399_; lean_object* v_fileName_400_; lean_object* v_fileMap_401_; lean_object* v_options_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v_initHeartbeats_405_; lean_object* v_maxHeartbeats_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; lean_object* v_cancelTk_x3f_409_; lean_object* v_inheritedTraceOptions_410_; lean_object* v___x_411_; uint16_t v___y_413_; lean_object* v___y_414_; lean_object* v_fileName_415_; lean_object* v_fileMap_416_; lean_object* v_currNamespace_417_; lean_object* v_openDecls_418_; lean_object* v_initHeartbeats_419_; lean_object* v_maxHeartbeats_420_; lean_object* v_quotContext_421_; lean_object* v_currMacroScope_422_; lean_object* v_cancelTk_x3f_423_; lean_object* v_inheritedTraceOptions_424_; lean_object* v_currRecDepth_425_; lean_object* v_ref_426_; uint8_t v_suppressElabErrors_427_; uint8_t v_isRecordingDeps_428_; lean_object* v___y_429_; uint16_t v___y_458_; uint8_t v___y_459_; lean_object* v___y_460_; uint16_t v___y_483_; uint8_t v___y_484_; lean_object* v___y_485_; uint8_t v___y_486_; uint16_t v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; uint8_t v___y_491_; lean_object* v___y_493_; 
v_toCold_394_ = lean_ctor_get(v___y_374_, 0);
v_val_395_ = lean_ctor_get(v_snd_381_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_snd_381_, 1);
v_currRecDepth_396_ = lean_ctor_get(v___y_374_, 1);
v_ref_397_ = lean_ctor_get(v___y_374_, 2);
v_suppressElabErrors_398_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*3 + 2);
v_isRecordingDeps_399_ = lean_ctor_get_uint8(v___y_374_, sizeof(void*)*3 + 3);
v_fileName_400_ = lean_ctor_get(v_toCold_394_, 0);
v_fileMap_401_ = lean_ctor_get(v_toCold_394_, 1);
v_options_402_ = lean_ctor_get(v_toCold_394_, 2);
v_currNamespace_403_ = lean_ctor_get(v_toCold_394_, 4);
v_openDecls_404_ = lean_ctor_get(v_toCold_394_, 5);
v_initHeartbeats_405_ = lean_ctor_get(v_toCold_394_, 6);
v_maxHeartbeats_406_ = lean_ctor_get(v_toCold_394_, 7);
v_quotContext_407_ = lean_ctor_get(v_toCold_394_, 8);
v_currMacroScope_408_ = lean_ctor_get(v_toCold_394_, 9);
v_cancelTk_x3f_409_ = lean_ctor_get(v_toCold_394_, 10);
v_inheritedTraceOptions_410_ = lean_ctor_get(v_toCold_394_, 11);
v___x_411_ = lean_box(1);
if (v_isRecordingDeps_399_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = l_Lean_pp_mvars;
lean_inc_ref(v_options_402_);
v___x_504_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_options_402_, v___x_503_, v_isRecordingDeps_399_);
v___y_493_ = v___x_504_;
goto v___jp_492_;
}
else
{
lean_object* v___x_505_; 
lean_inc_ref(v_options_402_);
v___x_505_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_402_);
v___y_493_ = v___x_505_;
goto v___jp_492_;
}
v___jp_412_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_430_ = l_Lean_maxRecDepth;
v___x_431_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v___y_414_, v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_432_, 0, v_fileName_415_);
lean_ctor_set(v___x_432_, 1, v_fileMap_416_);
lean_ctor_set(v___x_432_, 2, v___y_414_);
lean_ctor_set(v___x_432_, 3, v___x_431_);
lean_ctor_set(v___x_432_, 4, v_currNamespace_417_);
lean_ctor_set(v___x_432_, 5, v_openDecls_418_);
lean_ctor_set(v___x_432_, 6, v_initHeartbeats_419_);
lean_ctor_set(v___x_432_, 7, v_maxHeartbeats_420_);
lean_ctor_set(v___x_432_, 8, v_quotContext_421_);
lean_ctor_set(v___x_432_, 9, v_currMacroScope_422_);
lean_ctor_set(v___x_432_, 10, v_cancelTk_x3f_423_);
lean_ctor_set(v___x_432_, 11, v_inheritedTraceOptions_424_);
lean_inc(v_ref_426_);
lean_inc(v_currRecDepth_425_);
v___x_433_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_currRecDepth_425_);
lean_ctor_set(v___x_433_, 2, v_ref_426_);
lean_ctor_set_uint16(v___x_433_, sizeof(void*)*3, v___y_413_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*3 + 2, v_suppressElabErrors_427_);
lean_ctor_set_uint8(v___x_433_, sizeof(void*)*3 + 3, v_isRecordingDeps_428_);
v___x_434_ = l_Lean_PrettyPrinter_delab(v_val_395_, v___x_411_, v___y_372_, v___y_373_, v___x_433_, v___y_429_);
lean_dec_ref_known(v___x_433_, 3);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2));
v___x_437_ = l_Lean_PrettyPrinter_ppCategory(v___x_436_, v_a_435_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_437_, 1);
v___x_439_ = l_Std_Format_defWidth;
v___x_440_ = l_Std_Format_pretty(v_a_438_, v___x_439_, v___x_382_, v___x_382_);
v_value_385_ = v___x_440_;
goto v___jp_384_;
}
else
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
lean_dec_ref(v_bs_x27_383_);
lean_dec(v_fst_380_);
v_a_441_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___x_437_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___x_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
lean_dec_ref(v_bs_x27_383_);
lean_dec(v_fst_380_);
v_a_449_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_434_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_434_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
v___jp_457_:
{
lean_object* v___x_461_; lean_object* v_env_462_; lean_object* v_nextMacroScope_463_; lean_object* v_ngen_464_; lean_object* v_auxDeclNGen_465_; lean_object* v_traceState_466_; lean_object* v_recordedDeps_467_; lean_object* v_messages_468_; lean_object* v_infoState_469_; lean_object* v_snapshotTasks_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_480_; 
v___x_461_ = lean_st_ref_take(v___y_375_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
v_nextMacroScope_463_ = lean_ctor_get(v___x_461_, 1);
v_ngen_464_ = lean_ctor_get(v___x_461_, 2);
v_auxDeclNGen_465_ = lean_ctor_get(v___x_461_, 3);
v_traceState_466_ = lean_ctor_get(v___x_461_, 4);
v_recordedDeps_467_ = lean_ctor_get(v___x_461_, 6);
v_messages_468_ = lean_ctor_get(v___x_461_, 7);
v_infoState_469_ = lean_ctor_get(v___x_461_, 8);
v_snapshotTasks_470_ = lean_ctor_get(v___x_461_, 9);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v___x_461_, 5);
lean_dec(v_unused_481_);
v___x_472_ = v___x_461_;
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_snapshotTasks_470_);
lean_inc(v_infoState_469_);
lean_inc(v_messages_468_);
lean_inc(v_recordedDeps_467_);
lean_inc(v_traceState_466_);
lean_inc(v_auxDeclNGen_465_);
lean_inc(v_ngen_464_);
lean_inc(v_nextMacroScope_463_);
lean_inc(v_env_462_);
lean_dec(v___x_461_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_480_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = l_Lean_Kernel_enableDiag(v_env_462_, v___y_459_);
v___x_475_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 5, v___x_475_);
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_nextMacroScope_463_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_ngen_464_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_auxDeclNGen_465_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_traceState_466_);
lean_ctor_set(v_reuseFailAlloc_479_, 5, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_479_, 6, v_recordedDeps_467_);
lean_ctor_set(v_reuseFailAlloc_479_, 7, v_messages_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 8, v_infoState_469_);
lean_ctor_set(v_reuseFailAlloc_479_, 9, v_snapshotTasks_470_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_st_ref_put(v___y_375_, v___x_477_);
lean_inc_ref(v_inheritedTraceOptions_410_);
lean_inc(v_cancelTk_x3f_409_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc_ref(v_fileMap_401_);
lean_inc_ref(v_fileName_400_);
v___y_413_ = v___y_458_;
v___y_414_ = v___y_460_;
v_fileName_415_ = v_fileName_400_;
v_fileMap_416_ = v_fileMap_401_;
v_currNamespace_417_ = v_currNamespace_403_;
v_openDecls_418_ = v_openDecls_404_;
v_initHeartbeats_419_ = v_initHeartbeats_405_;
v_maxHeartbeats_420_ = v_maxHeartbeats_406_;
v_quotContext_421_ = v_quotContext_407_;
v_currMacroScope_422_ = v_currMacroScope_408_;
v_cancelTk_x3f_423_ = v_cancelTk_x3f_409_;
v_inheritedTraceOptions_424_ = v_inheritedTraceOptions_410_;
v_currRecDepth_425_ = v_currRecDepth_396_;
v_ref_426_ = v_ref_397_;
v_suppressElabErrors_427_ = v_suppressElabErrors_398_;
v_isRecordingDeps_428_ = v_isRecordingDeps_399_;
v___y_429_ = v___y_375_;
goto v___jp_412_;
}
}
}
v___jp_482_:
{
if (v___y_486_ == 0)
{
v___y_458_ = v___y_483_;
v___y_459_ = v___y_484_;
v___y_460_ = v___y_485_;
goto v___jp_457_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_410_);
lean_inc(v_cancelTk_x3f_409_);
lean_inc(v_currMacroScope_408_);
lean_inc(v_quotContext_407_);
lean_inc(v_maxHeartbeats_406_);
lean_inc(v_initHeartbeats_405_);
lean_inc(v_openDecls_404_);
lean_inc(v_currNamespace_403_);
lean_inc_ref(v_fileMap_401_);
lean_inc_ref(v_fileName_400_);
v___y_413_ = v___y_483_;
v___y_414_ = v___y_485_;
v_fileName_415_ = v_fileName_400_;
v_fileMap_416_ = v_fileMap_401_;
v_currNamespace_417_ = v_currNamespace_403_;
v_openDecls_418_ = v_openDecls_404_;
v_initHeartbeats_419_ = v_initHeartbeats_405_;
v_maxHeartbeats_420_ = v_maxHeartbeats_406_;
v_quotContext_421_ = v_quotContext_407_;
v_currMacroScope_422_ = v_currMacroScope_408_;
v_cancelTk_x3f_423_ = v_cancelTk_x3f_409_;
v_inheritedTraceOptions_424_ = v_inheritedTraceOptions_410_;
v_currRecDepth_425_ = v_currRecDepth_396_;
v_ref_426_ = v_ref_397_;
v_suppressElabErrors_427_ = v_suppressElabErrors_398_;
v_isRecordingDeps_428_ = v_isRecordingDeps_399_;
v___y_429_ = v___y_375_;
goto v___jp_412_;
}
}
v___jp_487_:
{
if (v___y_489_ == 0)
{
v___y_483_ = v___y_488_;
v___y_484_ = v___y_491_;
v___y_485_ = v___y_490_;
v___y_486_ = v___x_377_;
goto v___jp_482_;
}
else
{
v___y_458_ = v___y_488_;
v___y_459_ = v___y_491_;
v___y_460_ = v___y_490_;
goto v___jp_457_;
}
}
v___jp_492_:
{
uint16_t v___x_494_; lean_object* v___x_495_; lean_object* v_env_496_; uint8_t v___x_497_; uint16_t v___x_498_; uint16_t v___x_499_; uint16_t v___x_500_; uint8_t v___x_501_; 
v___x_494_ = l_Lean_OptionFlags_ofOptions(v___y_493_);
v___x_495_ = lean_st_ref_get(v___y_375_);
v_env_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_495_);
v___x_497_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_496_);
lean_dec_ref(v_env_496_);
v___x_498_ = 512;
v___x_499_ = lean_uint16_land(v___x_494_, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_uint16_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
if (v___x_377_ == 0)
{
v___y_488_ = v___x_494_;
v___y_489_ = v___x_497_;
v___y_490_ = v___y_493_;
v___y_491_ = v___x_377_;
goto v___jp_487_;
}
else
{
v___y_483_ = v___x_494_;
v___y_484_ = v___x_377_;
v___y_485_ = v___y_493_;
v___y_486_ = v___x_497_;
goto v___jp_482_;
}
}
else
{
uint8_t v___x_502_; 
v___x_502_ = 0;
v___y_488_ = v___x_494_;
v___y_489_ = v___x_497_;
v___y_490_ = v___y_493_;
v___y_491_ = v___x_502_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v_snd_381_);
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6));
v_value_385_ = v___x_506_;
goto v___jp_384_;
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; size_t v___x_390_; size_t v___x_391_; lean_object* v___x_392_; 
v___x_386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_380_, v___x_377_);
v___x_387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__0));
v___x_388_ = lean_string_append(v___x_386_, v___x_387_);
v___x_389_ = lean_string_append(v___x_388_, v_value_385_);
lean_dec_ref(v_value_385_);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_add(v_i_370_, v___x_390_);
v___x_392_ = lean_array_uset(v_bs_x27_383_, v_i_370_, v___x_389_);
v_i_370_ = v___x_391_;
v_bs_371_ = v___x_392_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_516_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_boxed_515_, v_i_boxed_516_, v_bs_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object* v_s_518_, lean_object* v_pos_519_){
_start:
{
lean_object* v_str_520_; lean_object* v_startInclusive_521_; lean_object* v_endExclusive_522_; lean_object* v___x_523_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v_decide_534_; 
v_str_520_ = lean_ctor_get(v_s_518_, 0);
v_startInclusive_521_ = lean_ctor_get(v_s_518_, 1);
v_endExclusive_522_ = lean_ctor_get(v_s_518_, 2);
v___x_523_ = lean_nat_add(v_startInclusive_521_, v_pos_519_);
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = lean_nat_sub(v_endExclusive_522_, v___x_523_);
v_decide_534_ = lean_nat_dec_eq(v___x_532_, v___x_533_);
lean_dec(v___x_533_);
if (v_decide_534_ == 0)
{
uint32_t v___x_535_; uint32_t v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_string_utf8_get_fast(v_str_520_, v___x_523_);
v___x_536_ = 32;
v___x_537_ = lean_uint32_dec_eq(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
uint32_t v___x_538_; uint8_t v___x_539_; 
v___x_538_ = 9;
v___x_539_ = lean_uint32_dec_eq(v___x_535_, v___x_538_);
if (v___x_539_ == 0)
{
uint32_t v___x_540_; uint8_t v___x_541_; 
v___x_540_ = 13;
v___x_541_ = lean_uint32_dec_eq(v___x_535_, v___x_540_);
if (v___x_541_ == 0)
{
uint32_t v___x_542_; uint8_t v___x_543_; 
v___x_542_ = 10;
v___x_543_ = lean_uint32_dec_eq(v___x_535_, v___x_542_);
if (v___x_543_ == 0)
{
lean_dec(v___x_523_);
return v_pos_519_;
}
else
{
goto v___jp_524_;
}
}
else
{
goto v___jp_524_;
}
}
else
{
goto v___jp_524_;
}
}
else
{
goto v___jp_524_;
}
}
else
{
lean_dec(v___x_523_);
return v_pos_519_;
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_525_ = lean_string_utf8_next_fast(v_str_520_, v___x_523_);
v___x_526_ = lean_nat_sub(v___x_525_, v___x_523_);
lean_dec(v___x_523_);
v___x_527_ = lean_nat_add(v_pos_519_, v___x_526_);
lean_dec(v___x_526_);
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_pos_519_, v___x_528_);
v___x_530_ = lean_nat_dec_le(v___x_529_, v___x_527_);
lean_dec(v___x_529_);
if (v___x_530_ == 0)
{
lean_dec(v___x_527_);
return v_pos_519_;
}
else
{
lean_dec(v_pos_519_);
v_pos_519_ = v___x_527_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object* v_s_544_, lean_object* v_pos_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v_s_544_, v_pos_545_);
lean_dec_ref(v_s_544_);
return v_res_546_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2));
v___x_552_ = l_Lean_stringToMessageData(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8));
v___x_560_ = lean_unsigned_to_nat(14u);
v___x_561_ = lean_unsigned_to_nat(22u);
v___x_562_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7));
v___x_563_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6));
v___x_564_ = l_mkPanicMessageWithDecl(v___x_563_, v___x_562_, v___x_561_, v___x_560_, v___x_559_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1(void){
_start:
{
uint32_t v___x_565_; lean_object* v___x_566_; 
v___x_565_ = 32;
v___x_566_ = lean_box_uint32(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(lean_object* v_fields_567_, lean_object* v_stx_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; 
lean_inc(v_stx_568_);
v___x_574_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(v_stx_568_);
if (lean_obj_tag(v___x_574_) == 1)
{
lean_object* v_val_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_808_; 
v_val_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_808_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_808_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_val_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_808_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
size_t v_sz_579_; size_t v___x_580_; lean_object* v___x_581_; 
v_sz_579_ = lean_array_size(v_fields_567_);
v___x_580_ = ((size_t)0ULL);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_579_, v___x_580_, v_fields_567_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_799_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_581_, 1);
v___x_583_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_568_, v_val_575_, v_a_571_);
lean_dec(v_stx_568_);
v_a_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_799_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_799_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_799_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
uint8_t v___x_588_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_658_; uint8_t v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_684_; lean_object* v___y_685_; uint8_t v___y_686_; lean_object* v___y_687_; uint8_t v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v_startInclusive_695_; lean_object* v_endExclusive_696_; lean_object* v___y_704_; lean_object* v___y_705_; uint8_t v___y_706_; lean_object* v___y_707_; uint8_t v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; uint8_t v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; uint8_t v___y_731_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_770_; lean_object* v___y_783_; uint8_t v___x_786_; 
v___x_588_ = 1;
v___x_786_ = lean_unbox(v_a_584_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = lean_array_to_list(v_a_582_);
v___x_788_ = lean_box(1);
v___x_789_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(v___x_787_, v___x_788_);
v___y_770_ = v___x_789_;
goto v___jp_769_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = lean_box(0);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_array_get_size(v_a_582_);
v___x_793_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_a_582_);
v___y_783_ = v___x_790_;
goto v___jp_782_;
}
else
{
uint8_t v___x_794_; 
v___x_794_ = lean_nat_dec_le(v___x_792_, v___x_792_);
if (v___x_794_ == 0)
{
if (v___x_793_ == 0)
{
lean_dec(v_a_582_);
v___y_783_ = v___x_790_;
goto v___jp_782_;
}
else
{
size_t v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_usize_of_nat(v___x_792_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_582_, v___x_580_, v___x_795_, v___x_790_);
lean_dec(v_a_582_);
v___y_783_ = v___x_796_;
goto v___jp_782_;
}
}
else
{
size_t v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_usize_of_nat(v___x_792_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_582_, v___x_580_, v___x_797_, v___x_790_);
lean_dec(v_a_582_);
v___y_783_ = v___x_798_;
goto v___jp_782_;
}
}
}
v___jp_589_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_594_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_571_);
v___x_595_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_596_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v___x_594_, v___x_595_);
lean_dec_ref(v___x_594_);
lean_inc(v___y_593_);
v___x_597_ = lean_apply_1(v___y_591_, v___y_593_);
v___x_598_ = l_Std_Format_pretty(v___y_592_, v___x_596_, v___y_590_, v___x_597_);
lean_dec(v___x_596_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 1);
lean_ctor_set(v___x_586_, 0, v___x_598_);
v___x_600_ = v___x_586_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_617_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1));
v___x_603_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
lean_ctor_set(v___x_603_, 2, v___x_601_);
lean_ctor_set(v___x_603_, 3, v___x_601_);
lean_ctor_set(v___x_603_, 4, v___x_601_);
lean_ctor_set(v___x_603_, 5, v___x_602_);
lean_inc(v___y_593_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___y_593_);
lean_ctor_set(v___x_604_, 1, v___y_593_);
v___x_605_ = l_Lean_Syntax_ofRange(v___x_604_, v___x_588_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 0, v___x_605_);
v___x_607_ = v___x_577_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_616_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; 
v___x_608_ = 0;
v___x_609_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_609_, 0, v___x_603_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___x_601_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*3, v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = lean_mk_empty_array_with_capacity(v___x_611_);
v___x_613_ = lean_array_push(v___x_612_, v___x_609_);
v___x_614_ = 0;
v___x_615_ = l_Lean_MessageData_hint(v___x_610_, v___x_613_, v___x_601_, v___x_601_, v___x_614_, v_a_571_, v_a_572_);
lean_dec_ref(v___x_613_);
return v___x_615_;
}
}
}
v___jp_618_:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_627_, 0, v_fst_625_);
lean_ctor_set(v___x_627_, 1, v___y_623_);
v___x_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v_snd_626_);
if (lean_obj_tag(v___y_620_) == 0)
{
if (lean_obj_tag(v___y_624_) == 0)
{
v___y_590_ = v___y_622_;
v___y_591_ = v___y_621_;
v___y_592_ = v___x_628_;
v___y_593_ = v___y_619_;
goto v___jp_589_;
}
else
{
lean_object* v_val_629_; 
lean_dec(v___y_619_);
v_val_629_ = lean_ctor_get(v___y_624_, 0);
lean_inc(v_val_629_);
lean_dec_ref_known(v___y_624_, 1);
v___y_590_ = v___y_622_;
v___y_591_ = v___y_621_;
v___y_592_ = v___x_628_;
v___y_593_ = v_val_629_;
goto v___jp_589_;
}
}
else
{
lean_object* v_val_630_; 
lean_dec(v___y_624_);
lean_dec(v___y_619_);
v_val_630_ = lean_ctor_get(v___y_620_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___y_620_, 1);
v___y_590_ = v___y_622_;
v___y_591_ = v___y_621_;
v___y_592_ = v___x_628_;
v___y_593_ = v_val_630_;
goto v___jp_589_;
}
}
v___jp_631_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(1);
v___x_639_ = lean_box(0);
v___y_619_ = v___y_632_;
v___y_620_ = v___y_633_;
v___y_621_ = v___y_635_;
v___y_622_ = v___y_634_;
v___y_623_ = v___y_636_;
v___y_624_ = v___y_637_;
v_fst_625_ = v___x_638_;
v_snd_626_ = v___x_639_;
goto v___jp_618_;
}
v___jp_640_:
{
if (lean_obj_tag(v___y_646_) == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_box(1);
v___x_648_ = lean_box(0);
v___y_619_ = v___y_641_;
v___y_620_ = v___y_642_;
v___y_621_ = v___y_644_;
v___y_622_ = v___y_643_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_646_;
v_fst_625_ = v___x_647_;
v_snd_626_ = v___x_648_;
goto v___jp_618_;
}
else
{
lean_object* v_val_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_val_649_ = lean_ctor_get(v___y_646_, 0);
lean_inc_ref(v___y_644_);
lean_inc(v_val_649_);
v___x_650_ = lean_apply_1(v___y_644_, v_val_649_);
v___x_651_ = lean_nat_sub(v___y_643_, v___x_650_);
lean_dec(v___x_650_);
v___x_652_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
v___x_653_ = l_List_replicateTR___redArg(v___x_651_, v___x_652_);
v___x_654_ = lean_string_mk(v___x_653_);
v___x_655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
v___x_656_ = lean_box(0);
v___y_619_ = v___y_641_;
v___y_620_ = v___y_642_;
v___y_621_ = v___y_644_;
v___y_622_ = v___y_643_;
v___y_623_ = v___y_645_;
v___y_624_ = v___y_646_;
v_fst_625_ = v___x_655_;
v_snd_626_ = v___x_656_;
goto v___jp_618_;
}
}
v___jp_657_:
{
uint8_t v___x_667_; 
v___x_667_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_nat_dec_lt(v___x_668_, v___y_664_);
lean_dec(v___y_664_);
if (v___x_669_ == 0)
{
if (v___y_661_ == 0)
{
if (v___y_659_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5));
v___y_619_ = v___y_658_;
v___y_620_ = v___y_660_;
v___y_621_ = v___y_663_;
v___y_622_ = v___y_662_;
v___y_623_ = v___y_665_;
v___y_624_ = v___y_666_;
v_fst_625_ = v___x_670_;
v_snd_626_ = v___x_670_;
goto v___jp_618_;
}
else
{
v___y_641_ = v___y_658_;
v___y_642_ = v___y_660_;
v___y_643_ = v___y_662_;
v___y_644_ = v___y_663_;
v___y_645_ = v___y_665_;
v___y_646_ = v___y_666_;
goto v___jp_640_;
}
}
else
{
if (v___y_659_ == 0)
{
v___y_632_ = v___y_658_;
v___y_633_ = v___y_660_;
v___y_634_ = v___y_662_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_665_;
v___y_637_ = v___y_666_;
goto v___jp_631_;
}
else
{
v___y_641_ = v___y_658_;
v___y_642_ = v___y_660_;
v___y_643_ = v___y_662_;
v___y_644_ = v___y_663_;
v___y_645_ = v___y_665_;
v___y_646_ = v___y_666_;
goto v___jp_640_;
}
}
}
else
{
v___y_632_ = v___y_658_;
v___y_633_ = v___y_660_;
v___y_634_ = v___y_662_;
v___y_635_ = v___y_663_;
v___y_636_ = v___y_665_;
v___y_637_ = v___y_666_;
goto v___jp_631_;
}
}
else
{
lean_object* v___x_671_; 
lean_dec(v___y_664_);
v___x_671_ = lean_box(0);
v___y_619_ = v___y_658_;
v___y_620_ = v___y_660_;
v___y_621_ = v___y_663_;
v___y_622_ = v___y_662_;
v___y_623_ = v___y_665_;
v___y_624_ = v___y_666_;
v_fst_625_ = v___x_671_;
v_snd_626_ = v___x_671_;
goto v___jp_618_;
}
}
v___jp_672_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___y_681_);
v___y_658_ = v___y_673_;
v___y_659_ = v___y_674_;
v___y_660_ = v___y_675_;
v___y_661_ = v___y_676_;
v___y_662_ = v___y_678_;
v___y_663_ = v___y_677_;
v___y_664_ = v___y_680_;
v___y_665_ = v___y_679_;
v___y_666_ = v___x_682_;
goto v___jp_657_;
}
v___jp_683_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v_decide_700_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___y_694_, v___x_697_);
lean_dec_ref(v___y_694_);
v___x_699_ = lean_nat_sub(v_endExclusive_696_, v_startInclusive_695_);
lean_dec(v_startInclusive_695_);
lean_dec(v_endExclusive_696_);
v_decide_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
lean_dec(v___x_699_);
lean_dec(v___x_698_);
if (v_decide_700_ == 0)
{
lean_object* v___x_701_; 
lean_dec(v___y_693_);
lean_dec(v___y_685_);
v___x_701_ = lean_box(0);
v___y_658_ = v___y_684_;
v___y_659_ = v___y_686_;
v___y_660_ = v___y_687_;
v___y_661_ = v___y_688_;
v___y_662_ = v___y_690_;
v___y_663_ = v___y_689_;
v___y_664_ = v___y_692_;
v___y_665_ = v___y_691_;
v___y_666_ = v___x_701_;
goto v___jp_657_;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = lean_nat_dec_le(v___y_693_, v___y_685_);
if (v___x_702_ == 0)
{
lean_dec(v___y_693_);
v___y_673_ = v___y_684_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_685_;
goto v___jp_672_;
}
else
{
lean_dec(v___y_685_);
v___y_673_ = v___y_684_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_687_;
v___y_676_ = v___y_688_;
v___y_677_ = v___y_689_;
v___y_678_ = v___y_690_;
v___y_679_ = v___y_691_;
v___y_680_ = v___y_692_;
v___y_681_ = v___y_693_;
goto v___jp_672_;
}
}
}
v___jp_703_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_startInclusive_716_; lean_object* v_endExclusive_717_; 
v___x_714_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9);
v___x_715_ = l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___x_714_);
v_startInclusive_716_ = lean_ctor_get(v___x_715_, 1);
lean_inc(v_startInclusive_716_);
v_endExclusive_717_ = lean_ctor_get(v___x_715_, 2);
lean_inc(v_endExclusive_717_);
v___y_684_ = v___y_704_;
v___y_685_ = v___y_705_;
v___y_686_ = v___y_706_;
v___y_687_ = v___y_707_;
v___y_688_ = v___y_708_;
v___y_689_ = v___y_710_;
v___y_690_ = v___y_709_;
v___y_691_ = v___y_712_;
v___y_692_ = v___y_711_;
v___y_693_ = v___y_713_;
v___y_694_ = v___x_715_;
v_startInclusive_695_ = v_startInclusive_716_;
v_endExclusive_696_ = v_endExclusive_717_;
goto v___jp_683_;
}
v___jp_718_:
{
if (v___y_727_ == 0)
{
lean_dec_ref(v___y_723_);
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_730_;
goto v___jp_703_;
}
else
{
if (v___y_731_ == 0)
{
lean_dec_ref(v___y_723_);
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_721_;
v___y_707_ = v___y_722_;
v___y_708_ = v___y_724_;
v___y_709_ = v___y_726_;
v___y_710_ = v___y_725_;
v___y_711_ = v___y_729_;
v___y_712_ = v___y_728_;
v___y_713_ = v___y_730_;
goto v___jp_703_;
}
else
{
lean_object* v___x_732_; 
lean_inc_n(v___y_720_, 2);
lean_inc_n(v___y_719_, 2);
v___x_732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_732_, 0, v___y_723_);
lean_ctor_set(v___x_732_, 1, v___y_719_);
lean_ctor_set(v___x_732_, 2, v___y_720_);
v___y_684_ = v___y_719_;
v___y_685_ = v___y_720_;
v___y_686_ = v___y_721_;
v___y_687_ = v___y_722_;
v___y_688_ = v___y_724_;
v___y_689_ = v___y_725_;
v___y_690_ = v___y_726_;
v___y_691_ = v___y_728_;
v___y_692_ = v___y_729_;
v___y_693_ = v___y_730_;
v___y_694_ = v___x_732_;
v_startInclusive_695_ = v___y_719_;
v_endExclusive_696_ = v___y_720_;
goto v___jp_683_;
}
}
}
v___jp_733_:
{
lean_object* v_lastFieldTailPos_x3f_738_; uint8_t v_hasWith_739_; lean_object* v_numFields_740_; lean_object* v_leaderPos_741_; lean_object* v_leaderTailPos_742_; lean_object* v_closingPos_743_; lean_object* v___x_744_; lean_object* v_line_745_; lean_object* v___x_746_; lean_object* v_line_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_lastFieldTailPos_x3f_738_ = lean_ctor_get(v_val_575_, 1);
lean_inc(v_lastFieldTailPos_x3f_738_);
v_hasWith_739_ = lean_ctor_get_uint8(v_val_575_, sizeof(void*)*7);
v_numFields_740_ = lean_ctor_get(v_val_575_, 2);
lean_inc(v_numFields_740_);
v_leaderPos_741_ = lean_ctor_get(v_val_575_, 4);
lean_inc(v_leaderPos_741_);
v_leaderTailPos_742_ = lean_ctor_get(v_val_575_, 5);
lean_inc(v_leaderTailPos_742_);
v_closingPos_743_ = lean_ctor_get(v_val_575_, 6);
lean_inc(v_closingPos_743_);
lean_dec(v_val_575_);
lean_inc_ref_n(v___y_734_, 2);
v___x_744_ = l_Lean_FileMap_utf8PosToLspPos(v___y_734_, v_leaderPos_741_);
lean_dec(v_leaderPos_741_);
v_line_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_line_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_FileMap_utf8PosToLspPos(v___y_734_, v_closingPos_743_);
lean_dec(v_closingPos_743_);
v_line_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_line_747_);
lean_dec_ref(v___x_746_);
v___x_748_ = lean_nat_dec_lt(v_line_745_, v_line_747_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_line_745_, v___x_749_);
lean_dec(v_line_745_);
v___x_751_ = lean_nat_dec_le(v_line_747_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v_line_747_);
if (v___x_751_ == 0)
{
lean_object* v_source_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; 
v_source_752_ = lean_ctor_get(v___y_734_, 0);
lean_inc_ref_n(v_source_752_, 3);
lean_dec_ref(v___y_734_);
v___x_753_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_752_, v_leaderTailPos_742_);
v___x_754_ = lean_nat_add(v___y_737_, v___x_749_);
lean_inc(v___x_753_);
v___x_755_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v_source_752_, v___x_754_, v___x_753_);
v___x_756_ = lean_string_utf8_next(v_source_752_, v___x_753_);
lean_dec(v___x_753_);
v___x_757_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_752_, v___x_756_);
lean_dec(v___x_756_);
v___x_758_ = lean_string_is_valid_pos(v_source_752_, v_leaderTailPos_742_);
v___x_759_ = lean_string_is_valid_pos(v_source_752_, v___x_757_);
if (v___x_759_ == 0)
{
v___y_719_ = v_leaderTailPos_742_;
v___y_720_ = v___x_757_;
v___y_721_ = v___x_748_;
v___y_722_ = v_lastFieldTailPos_x3f_738_;
v___y_723_ = v_source_752_;
v___y_724_ = v_hasWith_739_;
v___y_725_ = v___y_735_;
v___y_726_ = v___y_737_;
v___y_727_ = v___x_758_;
v___y_728_ = v___y_736_;
v___y_729_ = v_numFields_740_;
v___y_730_ = v___x_755_;
v___y_731_ = v___x_759_;
goto v___jp_718_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v_leaderTailPos_742_, v___x_757_);
v___y_719_ = v_leaderTailPos_742_;
v___y_720_ = v___x_757_;
v___y_721_ = v___x_748_;
v___y_722_ = v_lastFieldTailPos_x3f_738_;
v___y_723_ = v_source_752_;
v___y_724_ = v_hasWith_739_;
v___y_725_ = v___y_735_;
v___y_726_ = v___y_737_;
v___y_727_ = v___x_758_;
v___y_728_ = v___y_736_;
v___y_729_ = v_numFields_740_;
v___y_730_ = v___x_755_;
v___y_731_ = v___x_760_;
goto v___jp_718_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v___y_734_);
v___x_761_ = lean_box(0);
v___y_658_ = v_leaderTailPos_742_;
v___y_659_ = v___x_748_;
v___y_660_ = v_lastFieldTailPos_x3f_738_;
v___y_661_ = v_hasWith_739_;
v___y_662_ = v___y_737_;
v___y_663_ = v___y_735_;
v___y_664_ = v_numFields_740_;
v___y_665_ = v___y_736_;
v___y_666_ = v___x_761_;
goto v___jp_657_;
}
}
v___jp_762_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = lean_nat_add(v___y_766_, v___x_767_);
lean_dec(v___y_766_);
v___y_734_ = v___y_763_;
v___y_735_ = v___y_764_;
v___y_736_ = v___y_765_;
v___y_737_ = v___x_768_;
goto v___jp_733_;
}
v___jp_769_:
{
lean_object* v_toCold_771_; lean_object* v_fileMap_772_; lean_object* v_initFieldPos_x3f_773_; lean_object* v_openingPos_774_; lean_object* v_closingPos_775_; lean_object* v___f_776_; 
v_toCold_771_ = lean_ctor_get(v_a_571_, 0);
v_fileMap_772_ = lean_ctor_get(v_toCold_771_, 1);
v_initFieldPos_x3f_773_ = lean_ctor_get(v_val_575_, 0);
v_openingPos_774_ = lean_ctor_get(v_val_575_, 3);
v_closingPos_775_ = lean_ctor_get(v_val_575_, 6);
lean_inc_ref(v_fileMap_772_);
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed), 2, 1);
lean_closure_set(v___f_776_, 0, v_fileMap_772_);
if (lean_obj_tag(v_initFieldPos_x3f_773_) == 1)
{
lean_object* v_val_777_; lean_object* v___x_778_; 
v_val_777_ = lean_ctor_get(v_initFieldPos_x3f_773_, 0);
lean_inc_ref_n(v_fileMap_772_, 2);
v___x_778_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_772_, v_val_777_);
v___y_734_ = v_fileMap_772_;
v___y_735_ = v___f_776_;
v___y_736_ = v___y_770_;
v___y_737_ = v___x_778_;
goto v___jp_733_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_inc_ref_n(v_fileMap_772_, 2);
v___x_779_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_772_, v_openingPos_774_);
v___x_780_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_772_, v_closingPos_775_);
v___x_781_ = lean_nat_dec_le(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v___x_779_);
lean_inc_ref(v_fileMap_772_);
v___y_763_ = v_fileMap_772_;
v___y_764_ = v___f_776_;
v___y_765_ = v___y_770_;
v___y_766_ = v___x_780_;
goto v___jp_762_;
}
else
{
lean_dec(v___x_780_);
lean_inc_ref(v_fileMap_772_);
v___y_763_ = v_fileMap_772_;
v___y_764_ = v___f_776_;
v___y_765_ = v___y_770_;
v___y_766_ = v___x_779_;
goto v___jp_762_;
}
}
}
v___jp_782_:
{
uint8_t v___x_784_; lean_object* v___x_785_; 
v___x_784_ = 1;
v___x_785_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_785_, 0, v___y_783_);
lean_ctor_set_uint8(v___x_785_, sizeof(void*)*1, v___x_784_);
v___y_770_ = v___x_785_;
goto v___jp_769_;
}
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_del_object(v___x_577_);
lean_dec(v_val_575_);
lean_dec(v_stx_568_);
v_a_800_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_581_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_581_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v___x_574_);
lean_dec(v_stx_568_);
lean_dec_ref(v_fields_567_);
v___x_809_ = l_Lean_MessageData_nil;
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object* v_fields_811_, lean_object* v_stx_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_811_, v_stx_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(lean_object* v___x_819_, lean_object* v_n_820_, lean_object* v_j_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v___x_819_, v_j_821_, v_a_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object* v___x_825_, lean_object* v_n_826_, lean_object* v_j_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v___x_825_, v_n_826_, v_j_827_, v_a_828_, v_a_829_);
lean_dec(v_n_826_);
lean_dec_ref(v___x_825_);
return v_res_830_;
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
