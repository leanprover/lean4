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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
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
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_12_; uint8_t v___y_13_; lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; uint8_t v___y_23_; uint8_t v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v_fst_39_; uint8_t v_snd_40_; lean_object* v___x_67_; 
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
lean_ctor_set(v___x_20_, 0, v___y_16_);
lean_ctor_set(v___x_20_, 1, v___y_19_);
lean_ctor_set(v___x_20_, 2, v___y_12_);
lean_ctor_set(v___x_20_, 3, v___y_17_);
lean_ctor_set(v___x_20_, 4, v___y_15_);
lean_ctor_set(v___x_20_, 5, v___y_14_);
lean_ctor_set(v___x_20_, 6, v___y_18_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*7, v___y_13_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
v___jp_22_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_31_ = lean_array_get_size(v___y_28_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v___x_31_, v___x_32_);
v___x_34_ = lean_nat_dec_lt(v___x_33_, v___x_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___x_33_);
lean_dec_ref(v___y_28_);
v___x_35_ = lean_box(0);
v___y_12_ = v___x_31_;
v___y_13_ = v___y_23_;
v___y_14_ = v___y_25_;
v___y_15_ = v___y_26_;
v___y_16_ = v___y_30_;
v___y_17_ = v___y_27_;
v___y_18_ = v___y_29_;
v___y_19_ = v___x_35_;
goto v___jp_11_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_fget(v___y_28_, v___x_33_);
lean_dec(v___x_33_);
lean_dec_ref(v___y_28_);
v___x_37_ = l_Lean_Syntax_getTailPos_x3f(v___x_36_, v___y_24_);
lean_dec(v___x_36_);
v___y_12_ = v___x_31_;
v___y_13_ = v___y_23_;
v___y_14_ = v___y_25_;
v___y_15_ = v___y_26_;
v___y_16_ = v___y_30_;
v___y_17_ = v___y_27_;
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
v___y_23_ = v_snd_40_;
v___y_24_ = v___x_41_;
v___y_25_ = v_val_47_;
v___y_26_ = v_val_44_;
v___y_27_ = v_val_52_;
v___y_28_ = v___x_61_;
v___y_29_ = v_val_57_;
v___y_30_ = v___x_64_;
goto v___jp_22_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_array_fget(v___x_61_, v___x_48_);
v___x_66_ = l_Lean_Syntax_getPos_x3f(v___x_65_, v___x_41_);
lean_dec(v___x_65_);
v___y_23_ = v_snd_40_;
v___y_24_ = v___x_41_;
v___y_25_ = v_val_47_;
v___y_26_ = v_val_44_;
v___y_27_ = v_val_52_;
v___y_28_ = v___x_61_;
v___y_29_ = v_val_57_;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object* v_opts_235_, lean_object* v_opt_236_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object* v_opts_243_, lean_object* v_opt_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_243_, v_opt_244_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(lean_object* v_o_325_, lean_object* v_k_326_, uint8_t v_v_327_){
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
v___x_335_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(lean_object* v_o_344_, lean_object* v_k_345_, lean_object* v_v_346_){
_start:
{
uint8_t v_v_boxed_347_; lean_object* v_res_348_; 
v_v_boxed_347_ = lean_unbox(v_v_346_);
v_res_348_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_o_344_, v_k_345_, v_v_boxed_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object* v_opts_349_, lean_object* v_opt_350_, uint8_t v_val_351_){
_start:
{
lean_object* v_name_352_; lean_object* v___x_353_; 
v_name_352_ = lean_ctor_get(v_opt_350_, 0);
lean_inc(v_name_352_);
lean_dec_ref(v_opt_350_);
v___x_353_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_opts_349_, v_name_352_, v_val_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object* v_opts_354_, lean_object* v_opt_355_, lean_object* v_val_356_){
_start:
{
uint8_t v_val_boxed_357_; lean_object* v_res_358_; 
v_val_boxed_357_ = lean_unbox(v_val_356_);
v_res_358_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_opts_354_, v_opt_355_, v_val_boxed_357_);
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
lean_object* v_toCold_394_; lean_object* v_val_395_; lean_object* v_currRecDepth_396_; lean_object* v_ref_397_; uint8_t v_suppressElabErrors_398_; uint8_t v_isRecordingDeps_399_; lean_object* v_fileName_400_; lean_object* v_fileMap_401_; lean_object* v_options_402_; lean_object* v_currNamespace_403_; lean_object* v_openDecls_404_; lean_object* v_initHeartbeats_405_; lean_object* v_maxHeartbeats_406_; lean_object* v_quotContext_407_; lean_object* v_currMacroScope_408_; lean_object* v_cancelTk_x3f_409_; lean_object* v_inheritedTraceOptions_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; uint16_t v___x_415_; lean_object* v_fileName_417_; lean_object* v_fileMap_418_; lean_object* v_currNamespace_419_; lean_object* v_openDecls_420_; lean_object* v_initHeartbeats_421_; lean_object* v_maxHeartbeats_422_; lean_object* v_quotContext_423_; lean_object* v_currMacroScope_424_; lean_object* v_cancelTk_x3f_425_; lean_object* v_inheritedTraceOptions_426_; lean_object* v_currRecDepth_427_; lean_object* v_ref_428_; uint8_t v_suppressElabErrors_429_; uint8_t v_isRecordingDeps_430_; lean_object* v___y_431_; lean_object* v___x_459_; uint8_t v___y_461_; uint8_t v___y_484_; uint8_t v___y_485_; lean_object* v_env_486_; uint8_t v___x_487_; uint8_t v___y_489_; uint16_t v___x_490_; uint16_t v___x_491_; uint16_t v___x_492_; uint8_t v___x_493_; 
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
v___x_412_ = l_Lean_pp_mvars;
v___x_413_ = 0;
lean_inc_ref(v_options_402_);
v___x_414_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_options_402_, v___x_412_, v___x_413_);
v___x_415_ = l_Lean_OptionFlags_ofOptions(v___x_414_);
v___x_459_ = lean_st_ref_get(v___y_375_);
v_env_486_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_env_486_);
lean_dec(v___x_459_);
v___x_487_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_486_);
lean_dec_ref(v_env_486_);
v___x_490_ = 512;
v___x_491_ = lean_uint16_land(v___x_415_, v___x_490_);
v___x_492_ = 0;
v___x_493_ = lean_uint16_dec_eq(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
if (v___x_377_ == 0)
{
v___y_489_ = v___x_377_;
goto v___jp_488_;
}
else
{
v___y_484_ = v___x_377_;
v___y_485_ = v___x_487_;
goto v___jp_483_;
}
}
else
{
v___y_489_ = v___x_413_;
goto v___jp_488_;
}
v___jp_416_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_432_ = l_Lean_maxRecDepth;
v___x_433_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v___x_414_, v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_434_, 0, v_fileName_417_);
lean_ctor_set(v___x_434_, 1, v_fileMap_418_);
lean_ctor_set(v___x_434_, 2, v___x_414_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
lean_ctor_set(v___x_434_, 4, v_currNamespace_419_);
lean_ctor_set(v___x_434_, 5, v_openDecls_420_);
lean_ctor_set(v___x_434_, 6, v_initHeartbeats_421_);
lean_ctor_set(v___x_434_, 7, v_maxHeartbeats_422_);
lean_ctor_set(v___x_434_, 8, v_quotContext_423_);
lean_ctor_set(v___x_434_, 9, v_currMacroScope_424_);
lean_ctor_set(v___x_434_, 10, v_cancelTk_x3f_425_);
lean_ctor_set(v___x_434_, 11, v_inheritedTraceOptions_426_);
lean_inc(v_ref_428_);
lean_inc(v_currRecDepth_427_);
v___x_435_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_currRecDepth_427_);
lean_ctor_set(v___x_435_, 2, v_ref_428_);
lean_ctor_set_uint16(v___x_435_, sizeof(void*)*3, v___x_415_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*3 + 2, v_suppressElabErrors_429_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*3 + 3, v_isRecordingDeps_430_);
v___x_436_ = l_Lean_PrettyPrinter_delab(v_val_395_, v___x_411_, v___y_372_, v___y_373_, v___x_435_, v___y_431_);
lean_dec_ref_known(v___x_435_, 3);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__2));
v___x_439_ = l_Lean_PrettyPrinter_ppCategory(v___x_438_, v_a_437_, v___y_374_, v___y_375_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v___x_439_, 1);
v___x_441_ = l_Std_Format_defWidth;
v___x_442_ = l_Std_Format_pretty(v_a_440_, v___x_441_, v___x_382_, v___x_382_);
v_value_385_ = v___x_442_;
goto v___jp_384_;
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
lean_dec_ref(v_bs_x27_383_);
lean_dec(v_fst_380_);
v_a_443_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_439_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_439_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v_bs_x27_383_);
lean_dec(v_fst_380_);
v_a_451_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_436_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_436_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v_env_463_; lean_object* v_nextMacroScope_464_; lean_object* v_ngen_465_; lean_object* v_auxDeclNGen_466_; lean_object* v_traceState_467_; lean_object* v_recordedDeps_468_; lean_object* v_messages_469_; lean_object* v_infoState_470_; lean_object* v_snapshotTasks_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_481_; 
v___x_462_ = lean_st_ref_take(v___y_375_);
v_env_463_ = lean_ctor_get(v___x_462_, 0);
v_nextMacroScope_464_ = lean_ctor_get(v___x_462_, 1);
v_ngen_465_ = lean_ctor_get(v___x_462_, 2);
v_auxDeclNGen_466_ = lean_ctor_get(v___x_462_, 3);
v_traceState_467_ = lean_ctor_get(v___x_462_, 4);
v_recordedDeps_468_ = lean_ctor_get(v___x_462_, 6);
v_messages_469_ = lean_ctor_get(v___x_462_, 7);
v_infoState_470_ = lean_ctor_get(v___x_462_, 8);
v_snapshotTasks_471_ = lean_ctor_get(v___x_462_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v___x_462_, 5);
lean_dec(v_unused_482_);
v___x_473_ = v___x_462_;
v_isShared_474_ = v_isSharedCheck_481_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snapshotTasks_471_);
lean_inc(v_infoState_470_);
lean_inc(v_messages_469_);
lean_inc(v_recordedDeps_468_);
lean_inc(v_traceState_467_);
lean_inc(v_auxDeclNGen_466_);
lean_inc(v_ngen_465_);
lean_inc(v_nextMacroScope_464_);
lean_inc(v_env_463_);
lean_dec(v___x_462_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_481_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_475_ = l_Lean_Kernel_enableDiag(v_env_463_, v___y_461_);
v___x_476_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__5);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 5, v___x_476_);
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_478_ = v___x_473_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_nextMacroScope_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_ngen_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_auxDeclNGen_466_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_traceState_467_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_recordedDeps_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_messages_469_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v_infoState_470_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_snapshotTasks_471_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; 
v___x_479_ = lean_st_ref_put(v___y_375_, v___x_478_);
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
v_fileName_417_ = v_fileName_400_;
v_fileMap_418_ = v_fileMap_401_;
v_currNamespace_419_ = v_currNamespace_403_;
v_openDecls_420_ = v_openDecls_404_;
v_initHeartbeats_421_ = v_initHeartbeats_405_;
v_maxHeartbeats_422_ = v_maxHeartbeats_406_;
v_quotContext_423_ = v_quotContext_407_;
v_currMacroScope_424_ = v_currMacroScope_408_;
v_cancelTk_x3f_425_ = v_cancelTk_x3f_409_;
v_inheritedTraceOptions_426_ = v_inheritedTraceOptions_410_;
v_currRecDepth_427_ = v_currRecDepth_396_;
v_ref_428_ = v_ref_397_;
v_suppressElabErrors_429_ = v_suppressElabErrors_398_;
v_isRecordingDeps_430_ = v_isRecordingDeps_399_;
v___y_431_ = v___y_375_;
goto v___jp_416_;
}
}
}
v___jp_483_:
{
if (v___y_485_ == 0)
{
v___y_461_ = v___y_484_;
goto v___jp_460_;
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
v_fileName_417_ = v_fileName_400_;
v_fileMap_418_ = v_fileMap_401_;
v_currNamespace_419_ = v_currNamespace_403_;
v_openDecls_420_ = v_openDecls_404_;
v_initHeartbeats_421_ = v_initHeartbeats_405_;
v_maxHeartbeats_422_ = v_maxHeartbeats_406_;
v_quotContext_423_ = v_quotContext_407_;
v_currMacroScope_424_ = v_currMacroScope_408_;
v_cancelTk_x3f_425_ = v_cancelTk_x3f_409_;
v_inheritedTraceOptions_426_ = v_inheritedTraceOptions_410_;
v_currRecDepth_427_ = v_currRecDepth_396_;
v_ref_428_ = v_ref_397_;
v_suppressElabErrors_429_ = v_suppressElabErrors_398_;
v_isRecordingDeps_430_ = v_isRecordingDeps_399_;
v___y_431_ = v___y_375_;
goto v___jp_416_;
}
}
v___jp_488_:
{
if (v___x_487_ == 0)
{
v___y_484_ = v___y_489_;
v___y_485_ = v___x_377_;
goto v___jp_483_;
}
else
{
v___y_461_ = v___y_489_;
goto v___jp_460_;
}
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v_snd_381_);
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___closed__6));
v_value_385_ = v___x_494_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_bs_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_504_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_boxed_503_, v_i_boxed_504_, v_bs_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object* v_s_506_, lean_object* v_pos_507_){
_start:
{
lean_object* v_str_508_; lean_object* v_startInclusive_509_; lean_object* v_endExclusive_510_; lean_object* v___x_511_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v_decide_522_; 
v_str_508_ = lean_ctor_get(v_s_506_, 0);
v_startInclusive_509_ = lean_ctor_get(v_s_506_, 1);
v_endExclusive_510_ = lean_ctor_get(v_s_506_, 2);
v___x_511_ = lean_nat_add(v_startInclusive_509_, v_pos_507_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_sub(v_endExclusive_510_, v___x_511_);
v_decide_522_ = lean_nat_dec_eq(v___x_520_, v___x_521_);
lean_dec(v___x_521_);
if (v_decide_522_ == 0)
{
uint32_t v___x_523_; uint32_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_string_utf8_get_fast(v_str_508_, v___x_511_);
v___x_524_ = 32;
v___x_525_ = lean_uint32_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
uint32_t v___x_526_; uint8_t v___x_527_; 
v___x_526_ = 9;
v___x_527_ = lean_uint32_dec_eq(v___x_523_, v___x_526_);
if (v___x_527_ == 0)
{
uint32_t v___x_528_; uint8_t v___x_529_; 
v___x_528_ = 13;
v___x_529_ = lean_uint32_dec_eq(v___x_523_, v___x_528_);
if (v___x_529_ == 0)
{
uint32_t v___x_530_; uint8_t v___x_531_; 
v___x_530_ = 10;
v___x_531_ = lean_uint32_dec_eq(v___x_523_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec(v___x_511_);
return v_pos_507_;
}
else
{
goto v___jp_512_;
}
}
else
{
goto v___jp_512_;
}
}
else
{
goto v___jp_512_;
}
}
else
{
goto v___jp_512_;
}
}
else
{
lean_dec(v___x_511_);
return v_pos_507_;
}
v___jp_512_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_513_ = lean_string_utf8_next_fast(v_str_508_, v___x_511_);
v___x_514_ = lean_nat_sub(v___x_513_, v___x_511_);
lean_dec(v___x_511_);
v___x_515_ = lean_nat_add(v_pos_507_, v___x_514_);
lean_dec(v___x_514_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_pos_507_, v___x_516_);
v___x_518_ = lean_nat_dec_le(v___x_517_, v___x_515_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
lean_dec(v___x_515_);
return v_pos_507_;
}
else
{
lean_dec(v_pos_507_);
v_pos_507_ = v___x_515_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object* v_s_532_, lean_object* v_pos_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v_s_532_, v_pos_533_);
lean_dec_ref(v_s_532_);
return v_res_534_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_547_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8));
v___x_548_ = lean_unsigned_to_nat(14u);
v___x_549_ = lean_unsigned_to_nat(22u);
v___x_550_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7));
v___x_551_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6));
v___x_552_ = l_mkPanicMessageWithDecl(v___x_551_, v___x_550_, v___x_549_, v___x_548_, v___x_547_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1(void){
_start:
{
uint32_t v___x_553_; lean_object* v___x_554_; 
v___x_553_ = 32;
v___x_554_ = lean_box_uint32(v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(lean_object* v_fields_555_, lean_object* v_stx_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_562_; 
lean_inc(v_stx_556_);
v___x_562_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(v_stx_556_);
if (lean_obj_tag(v___x_562_) == 1)
{
lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_796_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_796_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_796_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_796_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v_sz_567_; size_t v___x_568_; lean_object* v___x_569_; 
v_sz_567_ = lean_array_size(v_fields_555_);
v___x_568_ = ((size_t)0ULL);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_sz_567_, v___x_568_, v_fields_555_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_787_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_556_, v_val_563_, v_a_559_);
lean_dec(v_stx_556_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_787_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_787_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_787_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
uint8_t v___x_576_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_661_; uint8_t v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; uint8_t v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_672_; lean_object* v___y_673_; uint8_t v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; uint8_t v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v_startInclusive_683_; lean_object* v_endExclusive_684_; lean_object* v___y_692_; lean_object* v___y_693_; uint8_t v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; uint8_t v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_707_; lean_object* v___y_708_; uint8_t v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; uint8_t v___y_713_; uint8_t v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_758_; lean_object* v___y_771_; uint8_t v___x_774_; 
v___x_576_ = 1;
v___x_774_ = lean_unbox(v_a_572_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_array_to_list(v_a_570_);
v___x_776_ = lean_box(1);
v___x_777_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(v___x_775_, v___x_776_);
v___y_758_ = v___x_777_;
goto v___jp_757_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_778_ = lean_box(0);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_array_get_size(v_a_570_);
v___x_781_ = lean_nat_dec_lt(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v_a_570_);
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = lean_nat_dec_le(v___x_780_, v___x_780_);
if (v___x_782_ == 0)
{
if (v___x_781_ == 0)
{
lean_dec(v_a_570_);
v___y_771_ = v___x_778_;
goto v___jp_770_;
}
else
{
size_t v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_usize_of_nat(v___x_780_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_570_, v___x_568_, v___x_783_, v___x_778_);
lean_dec(v_a_570_);
v___y_771_ = v___x_784_;
goto v___jp_770_;
}
}
else
{
size_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_usize_of_nat(v___x_780_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v_a_570_, v___x_568_, v___x_785_, v___x_778_);
lean_dec(v_a_570_);
v___y_771_ = v___x_786_;
goto v___jp_770_;
}
}
}
v___jp_577_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_582_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_559_);
v___x_583_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_584_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v___x_582_, v___x_583_);
lean_dec_ref(v___x_582_);
lean_inc(v___y_581_);
v___x_585_ = lean_apply_1(v___y_580_, v___y_581_);
v___x_586_ = l_Std_Format_pretty(v___y_579_, v___x_584_, v___y_578_, v___x_585_);
lean_dec(v___x_584_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v___x_586_);
v___x_588_ = v___x_574_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_605_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_589_ = lean_box(0);
v___x_590_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1));
v___x_591_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
lean_ctor_set(v___x_591_, 2, v___x_589_);
lean_ctor_set(v___x_591_, 3, v___x_589_);
lean_ctor_set(v___x_591_, 4, v___x_589_);
lean_ctor_set(v___x_591_, 5, v___x_590_);
lean_inc(v___y_581_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___y_581_);
lean_ctor_set(v___x_592_, 1, v___y_581_);
v___x_593_ = l_Lean_Syntax_ofRange(v___x_592_, v___x_576_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_593_);
v___x_595_ = v___x_565_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_604_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; 
v___x_596_ = 0;
v___x_597_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_597_, 0, v___x_591_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___x_589_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*3, v___x_596_);
v___x_598_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_array_push(v___x_600_, v___x_597_);
v___x_602_ = 0;
v___x_603_ = l_Lean_MessageData_hint(v___x_598_, v___x_601_, v___x_589_, v___x_589_, v___x_602_, v_a_559_, v_a_560_);
lean_dec_ref(v___x_601_);
return v___x_603_;
}
}
}
v___jp_606_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v_fst_613_);
lean_ctor_set(v___x_615_, 1, v___y_611_);
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_snd_614_);
if (lean_obj_tag(v___y_610_) == 0)
{
if (lean_obj_tag(v___y_609_) == 0)
{
v___y_578_ = v___y_607_;
v___y_579_ = v___x_616_;
v___y_580_ = v___y_608_;
v___y_581_ = v___y_612_;
goto v___jp_577_;
}
else
{
lean_object* v_val_617_; 
lean_dec(v___y_612_);
v_val_617_ = lean_ctor_get(v___y_609_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___y_609_, 1);
v___y_578_ = v___y_607_;
v___y_579_ = v___x_616_;
v___y_580_ = v___y_608_;
v___y_581_ = v_val_617_;
goto v___jp_577_;
}
}
else
{
lean_object* v_val_618_; 
lean_dec(v___y_612_);
lean_dec(v___y_609_);
v_val_618_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v___y_610_, 1);
v___y_578_ = v___y_607_;
v___y_579_ = v___x_616_;
v___y_580_ = v___y_608_;
v___y_581_ = v_val_618_;
goto v___jp_577_;
}
}
v___jp_619_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_box(1);
v___x_627_ = lean_box(0);
v___y_607_ = v___y_620_;
v___y_608_ = v___y_621_;
v___y_609_ = v___y_622_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_623_;
v___y_612_ = v___y_625_;
v_fst_613_ = v___x_626_;
v_snd_614_ = v___x_627_;
goto v___jp_606_;
}
v___jp_628_:
{
if (lean_obj_tag(v___y_631_) == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_box(1);
v___x_636_ = lean_box(0);
v___y_607_ = v___y_629_;
v___y_608_ = v___y_630_;
v___y_609_ = v___y_631_;
v___y_610_ = v___y_633_;
v___y_611_ = v___y_632_;
v___y_612_ = v___y_634_;
v_fst_613_ = v___x_635_;
v_snd_614_ = v___x_636_;
goto v___jp_606_;
}
else
{
lean_object* v_val_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_val_637_ = lean_ctor_get(v___y_631_, 0);
lean_inc_ref(v___y_630_);
lean_inc(v_val_637_);
v___x_638_ = lean_apply_1(v___y_630_, v_val_637_);
v___x_639_ = lean_nat_sub(v___y_629_, v___x_638_);
lean_dec(v___x_638_);
v___x_640_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
v___x_641_ = l_List_replicateTR___redArg(v___x_639_, v___x_640_);
v___x_642_ = lean_string_mk(v___x_641_);
v___x_643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_box(0);
v___y_607_ = v___y_629_;
v___y_608_ = v___y_630_;
v___y_609_ = v___y_631_;
v___y_610_ = v___y_633_;
v___y_611_ = v___y_632_;
v___y_612_ = v___y_634_;
v_fst_613_ = v___x_643_;
v_snd_614_ = v___x_644_;
goto v___jp_606_;
}
}
v___jp_645_:
{
uint8_t v___x_655_; 
v___x_655_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_nat_dec_lt(v___x_656_, v___y_649_);
lean_dec(v___y_649_);
if (v___x_657_ == 0)
{
if (v___y_647_ == 0)
{
if (v___y_650_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5));
v___y_607_ = v___y_646_;
v___y_608_ = v___y_648_;
v___y_609_ = v___y_654_;
v___y_610_ = v___y_652_;
v___y_611_ = v___y_651_;
v___y_612_ = v___y_653_;
v_fst_613_ = v___x_658_;
v_snd_614_ = v___x_658_;
goto v___jp_606_;
}
else
{
v___y_629_ = v___y_646_;
v___y_630_ = v___y_648_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_651_;
v___y_633_ = v___y_652_;
v___y_634_ = v___y_653_;
goto v___jp_628_;
}
}
else
{
if (v___y_650_ == 0)
{
v___y_620_ = v___y_646_;
v___y_621_ = v___y_648_;
v___y_622_ = v___y_654_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
goto v___jp_619_;
}
else
{
v___y_629_ = v___y_646_;
v___y_630_ = v___y_648_;
v___y_631_ = v___y_654_;
v___y_632_ = v___y_651_;
v___y_633_ = v___y_652_;
v___y_634_ = v___y_653_;
goto v___jp_628_;
}
}
}
else
{
v___y_620_ = v___y_646_;
v___y_621_ = v___y_648_;
v___y_622_ = v___y_654_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
goto v___jp_619_;
}
}
else
{
lean_object* v___x_659_; 
lean_dec(v___y_649_);
v___x_659_ = lean_box(0);
v___y_607_ = v___y_646_;
v___y_608_ = v___y_648_;
v___y_609_ = v___y_654_;
v___y_610_ = v___y_652_;
v___y_611_ = v___y_651_;
v___y_612_ = v___y_653_;
v_fst_613_ = v___x_659_;
v_snd_614_ = v___x_659_;
goto v___jp_606_;
}
}
v___jp_660_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___y_669_);
v___y_646_ = v___y_661_;
v___y_647_ = v___y_662_;
v___y_648_ = v___y_663_;
v___y_649_ = v___y_664_;
v___y_650_ = v___y_665_;
v___y_651_ = v___y_667_;
v___y_652_ = v___y_666_;
v___y_653_ = v___y_668_;
v___y_654_ = v___x_670_;
goto v___jp_645_;
}
v___jp_671_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v_decide_688_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___y_682_, v___x_685_);
lean_dec_ref(v___y_682_);
v___x_687_ = lean_nat_sub(v_endExclusive_684_, v_startInclusive_683_);
lean_dec(v_startInclusive_683_);
lean_dec(v_endExclusive_684_);
v_decide_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
lean_dec(v___x_687_);
lean_dec(v___x_686_);
if (v_decide_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___y_678_);
lean_dec(v___y_673_);
v___x_689_ = lean_box(0);
v___y_646_ = v___y_672_;
v___y_647_ = v___y_674_;
v___y_648_ = v___y_675_;
v___y_649_ = v___y_676_;
v___y_650_ = v___y_677_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_679_;
v___y_653_ = v___y_681_;
v___y_654_ = v___x_689_;
goto v___jp_645_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_le(v___y_678_, v___y_673_);
if (v___x_690_ == 0)
{
lean_dec(v___y_678_);
v___y_661_ = v___y_672_;
v___y_662_ = v___y_674_;
v___y_663_ = v___y_675_;
v___y_664_ = v___y_676_;
v___y_665_ = v___y_677_;
v___y_666_ = v___y_679_;
v___y_667_ = v___y_680_;
v___y_668_ = v___y_681_;
v___y_669_ = v___y_673_;
goto v___jp_660_;
}
else
{
lean_dec(v___y_673_);
v___y_661_ = v___y_672_;
v___y_662_ = v___y_674_;
v___y_663_ = v___y_675_;
v___y_664_ = v___y_676_;
v___y_665_ = v___y_677_;
v___y_666_ = v___y_679_;
v___y_667_ = v___y_680_;
v___y_668_ = v___y_681_;
v___y_669_ = v___y_678_;
goto v___jp_660_;
}
}
}
v___jp_691_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_startInclusive_704_; lean_object* v_endExclusive_705_; 
v___x_702_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9);
v___x_703_ = l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___x_702_);
v_startInclusive_704_ = lean_ctor_get(v___x_703_, 1);
lean_inc(v_startInclusive_704_);
v_endExclusive_705_ = lean_ctor_get(v___x_703_, 2);
lean_inc(v_endExclusive_705_);
v___y_672_ = v___y_692_;
v___y_673_ = v___y_693_;
v___y_674_ = v___y_694_;
v___y_675_ = v___y_695_;
v___y_676_ = v___y_696_;
v___y_677_ = v___y_697_;
v___y_678_ = v___y_700_;
v___y_679_ = v___y_699_;
v___y_680_ = v___y_698_;
v___y_681_ = v___y_701_;
v___y_682_ = v___x_703_;
v_startInclusive_683_ = v_startInclusive_704_;
v_endExclusive_684_ = v_endExclusive_705_;
goto v___jp_671_;
}
v___jp_706_:
{
if (v___y_714_ == 0)
{
lean_dec_ref(v___y_712_);
v___y_692_ = v___y_707_;
v___y_693_ = v___y_708_;
v___y_694_ = v___y_709_;
v___y_695_ = v___y_710_;
v___y_696_ = v___y_711_;
v___y_697_ = v___y_713_;
v___y_698_ = v___y_717_;
v___y_699_ = v___y_716_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_718_;
goto v___jp_691_;
}
else
{
if (v___y_719_ == 0)
{
lean_dec_ref(v___y_712_);
v___y_692_ = v___y_707_;
v___y_693_ = v___y_708_;
v___y_694_ = v___y_709_;
v___y_695_ = v___y_710_;
v___y_696_ = v___y_711_;
v___y_697_ = v___y_713_;
v___y_698_ = v___y_717_;
v___y_699_ = v___y_716_;
v___y_700_ = v___y_715_;
v___y_701_ = v___y_718_;
goto v___jp_691_;
}
else
{
lean_object* v___x_720_; 
lean_inc_n(v___y_708_, 2);
lean_inc_n(v___y_718_, 2);
v___x_720_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_720_, 0, v___y_712_);
lean_ctor_set(v___x_720_, 1, v___y_718_);
lean_ctor_set(v___x_720_, 2, v___y_708_);
v___y_672_ = v___y_707_;
v___y_673_ = v___y_708_;
v___y_674_ = v___y_709_;
v___y_675_ = v___y_710_;
v___y_676_ = v___y_711_;
v___y_677_ = v___y_713_;
v___y_678_ = v___y_715_;
v___y_679_ = v___y_716_;
v___y_680_ = v___y_717_;
v___y_681_ = v___y_718_;
v___y_682_ = v___x_720_;
v_startInclusive_683_ = v___y_718_;
v_endExclusive_684_ = v___y_708_;
goto v___jp_671_;
}
}
}
v___jp_721_:
{
lean_object* v_lastFieldTailPos_x3f_726_; uint8_t v_hasWith_727_; lean_object* v_numFields_728_; lean_object* v_leaderPos_729_; lean_object* v_leaderTailPos_730_; lean_object* v_closingPos_731_; lean_object* v___x_732_; lean_object* v_line_733_; lean_object* v___x_734_; lean_object* v_line_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_lastFieldTailPos_x3f_726_ = lean_ctor_get(v_val_563_, 1);
lean_inc(v_lastFieldTailPos_x3f_726_);
v_hasWith_727_ = lean_ctor_get_uint8(v_val_563_, sizeof(void*)*7);
v_numFields_728_ = lean_ctor_get(v_val_563_, 2);
lean_inc(v_numFields_728_);
v_leaderPos_729_ = lean_ctor_get(v_val_563_, 4);
lean_inc(v_leaderPos_729_);
v_leaderTailPos_730_ = lean_ctor_get(v_val_563_, 5);
lean_inc(v_leaderTailPos_730_);
v_closingPos_731_ = lean_ctor_get(v_val_563_, 6);
lean_inc(v_closingPos_731_);
lean_dec(v_val_563_);
lean_inc_ref_n(v___y_722_, 2);
v___x_732_ = l_Lean_FileMap_utf8PosToLspPos(v___y_722_, v_leaderPos_729_);
lean_dec(v_leaderPos_729_);
v_line_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_line_733_);
lean_dec_ref(v___x_732_);
v___x_734_ = l_Lean_FileMap_utf8PosToLspPos(v___y_722_, v_closingPos_731_);
lean_dec(v_closingPos_731_);
v_line_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_line_735_);
lean_dec_ref(v___x_734_);
v___x_736_ = lean_nat_dec_lt(v_line_733_, v_line_735_);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_line_733_, v___x_737_);
lean_dec(v_line_733_);
v___x_739_ = lean_nat_dec_le(v_line_735_, v___x_738_);
lean_dec(v___x_738_);
lean_dec(v_line_735_);
if (v___x_739_ == 0)
{
lean_object* v_source_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; 
v_source_740_ = lean_ctor_get(v___y_722_, 0);
lean_inc_ref_n(v_source_740_, 3);
lean_dec_ref(v___y_722_);
v___x_741_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_740_, v_leaderTailPos_730_);
v___x_742_ = lean_nat_add(v___y_725_, v___x_737_);
lean_inc(v___x_741_);
v___x_743_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v_source_740_, v___x_742_, v___x_741_);
v___x_744_ = lean_string_utf8_next(v_source_740_, v___x_741_);
lean_dec(v___x_741_);
v___x_745_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_740_, v___x_744_);
lean_dec(v___x_744_);
v___x_746_ = lean_string_is_valid_pos(v_source_740_, v_leaderTailPos_730_);
v___x_747_ = lean_string_is_valid_pos(v_source_740_, v___x_745_);
if (v___x_747_ == 0)
{
v___y_707_ = v___y_725_;
v___y_708_ = v___x_745_;
v___y_709_ = v_hasWith_727_;
v___y_710_ = v___y_723_;
v___y_711_ = v_numFields_728_;
v___y_712_ = v_source_740_;
v___y_713_ = v___x_736_;
v___y_714_ = v___x_746_;
v___y_715_ = v___x_743_;
v___y_716_ = v_lastFieldTailPos_x3f_726_;
v___y_717_ = v___y_724_;
v___y_718_ = v_leaderTailPos_730_;
v___y_719_ = v___x_747_;
goto v___jp_706_;
}
else
{
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_le(v_leaderTailPos_730_, v___x_745_);
v___y_707_ = v___y_725_;
v___y_708_ = v___x_745_;
v___y_709_ = v_hasWith_727_;
v___y_710_ = v___y_723_;
v___y_711_ = v_numFields_728_;
v___y_712_ = v_source_740_;
v___y_713_ = v___x_736_;
v___y_714_ = v___x_746_;
v___y_715_ = v___x_743_;
v___y_716_ = v_lastFieldTailPos_x3f_726_;
v___y_717_ = v___y_724_;
v___y_718_ = v_leaderTailPos_730_;
v___y_719_ = v___x_748_;
goto v___jp_706_;
}
}
else
{
lean_object* v___x_749_; 
lean_dec_ref(v___y_722_);
v___x_749_ = lean_box(0);
v___y_646_ = v___y_725_;
v___y_647_ = v_hasWith_727_;
v___y_648_ = v___y_723_;
v___y_649_ = v_numFields_728_;
v___y_650_ = v___x_736_;
v___y_651_ = v___y_724_;
v___y_652_ = v_lastFieldTailPos_x3f_726_;
v___y_653_ = v_leaderTailPos_730_;
v___y_654_ = v___x_749_;
goto v___jp_645_;
}
}
v___jp_750_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_unsigned_to_nat(2u);
v___x_756_ = lean_nat_add(v___y_754_, v___x_755_);
lean_dec(v___y_754_);
v___y_722_ = v___y_751_;
v___y_723_ = v___y_752_;
v___y_724_ = v___y_753_;
v___y_725_ = v___x_756_;
goto v___jp_721_;
}
v___jp_757_:
{
lean_object* v_toCold_759_; lean_object* v_fileMap_760_; lean_object* v_initFieldPos_x3f_761_; lean_object* v_openingPos_762_; lean_object* v_closingPos_763_; lean_object* v___f_764_; 
v_toCold_759_ = lean_ctor_get(v_a_559_, 0);
v_fileMap_760_ = lean_ctor_get(v_toCold_759_, 1);
v_initFieldPos_x3f_761_ = lean_ctor_get(v_val_563_, 0);
v_openingPos_762_ = lean_ctor_get(v_val_563_, 3);
v_closingPos_763_ = lean_ctor_get(v_val_563_, 6);
lean_inc_ref(v_fileMap_760_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed), 2, 1);
lean_closure_set(v___f_764_, 0, v_fileMap_760_);
if (lean_obj_tag(v_initFieldPos_x3f_761_) == 1)
{
lean_object* v_val_765_; lean_object* v___x_766_; 
v_val_765_ = lean_ctor_get(v_initFieldPos_x3f_761_, 0);
lean_inc_ref_n(v_fileMap_760_, 2);
v___x_766_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_760_, v_val_765_);
v___y_722_ = v_fileMap_760_;
v___y_723_ = v___f_764_;
v___y_724_ = v___y_758_;
v___y_725_ = v___x_766_;
goto v___jp_721_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
lean_inc_ref_n(v_fileMap_760_, 2);
v___x_767_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_760_, v_openingPos_762_);
v___x_768_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_760_, v_closingPos_763_);
v___x_769_ = lean_nat_dec_le(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v___x_767_);
lean_inc_ref(v_fileMap_760_);
v___y_751_ = v_fileMap_760_;
v___y_752_ = v___f_764_;
v___y_753_ = v___y_758_;
v___y_754_ = v___x_768_;
goto v___jp_750_;
}
else
{
lean_dec(v___x_768_);
lean_inc_ref(v_fileMap_760_);
v___y_751_ = v_fileMap_760_;
v___y_752_ = v___f_764_;
v___y_753_ = v___y_758_;
v___y_754_ = v___x_767_;
goto v___jp_750_;
}
}
}
v___jp_770_:
{
uint8_t v___x_772_; lean_object* v___x_773_; 
v___x_772_ = 1;
v___x_773_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_773_, 0, v___y_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*1, v___x_772_);
v___y_758_ = v___x_773_;
goto v___jp_757_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_del_object(v___x_565_);
lean_dec(v_val_563_);
lean_dec(v_stx_556_);
v_a_788_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_569_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_569_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___x_562_);
lean_dec(v_stx_556_);
lean_dec_ref(v_fields_555_);
v___x_797_ = l_Lean_MessageData_nil;
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object* v_fields_799_, lean_object* v_stx_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_799_, v_stx_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(lean_object* v___x_807_, lean_object* v_n_808_, lean_object* v_j_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___redArg(v___x_807_, v_j_809_, v_a_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object* v___x_813_, lean_object* v_n_814_, lean_object* v_j_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v___x_813_, v_n_814_, v_j_815_, v_a_816_, v_a_817_);
lean_dec(v_n_814_);
lean_dec_ref(v___x_813_);
return v_res_818_;
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
