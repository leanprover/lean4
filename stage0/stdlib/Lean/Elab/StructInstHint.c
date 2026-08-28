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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object*);
static const lean_string_object l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Add missing fields"};
static const lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(lean_object* v_stx_10_){
_start:
{
lean_object* v___y_12_; lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v___y_15_; lean_object* v___y_16_; uint8_t v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; uint8_t v___y_26_; lean_object* v___y_27_; uint8_t v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v_fst_39_; uint8_t v_snd_40_; lean_object* v___x_67_; 
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
lean_ctor_set(v___x_20_, 0, v___y_14_);
lean_ctor_set(v___x_20_, 1, v___y_19_);
lean_ctor_set(v___x_20_, 2, v___y_13_);
lean_ctor_set(v___x_20_, 3, v___y_16_);
lean_ctor_set(v___x_20_, 4, v___y_12_);
lean_ctor_set(v___x_20_, 5, v___y_15_);
lean_ctor_set(v___x_20_, 6, v___y_18_);
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*7, v___y_17_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
v___jp_22_:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
v___x_31_ = lean_array_get_size(v___y_24_);
v___x_32_ = lean_unsigned_to_nat(1u);
v___x_33_ = lean_nat_sub(v___x_31_, v___x_32_);
v___x_34_ = lean_nat_dec_lt(v___x_33_, v___x_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
lean_dec(v___x_33_);
lean_dec_ref(v___y_24_);
v___x_35_ = lean_box(0);
v___y_12_ = v___y_23_;
v___y_13_ = v___x_31_;
v___y_14_ = v___y_30_;
v___y_15_ = v___y_25_;
v___y_16_ = v___y_27_;
v___y_17_ = v___y_28_;
v___y_18_ = v___y_29_;
v___y_19_ = v___x_35_;
goto v___jp_11_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_array_fget(v___y_24_, v___x_33_);
lean_dec(v___x_33_);
lean_dec_ref(v___y_24_);
v___x_37_ = l_Lean_Syntax_getTailPos_x3f(v___x_36_, v___y_26_);
lean_dec(v___x_36_);
v___y_12_ = v___y_23_;
v___y_13_ = v___x_31_;
v___y_14_ = v___y_30_;
v___y_15_ = v___y_25_;
v___y_16_ = v___y_27_;
v___y_17_ = v___y_28_;
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
v___y_24_ = v___x_61_;
v___y_25_ = v_val_47_;
v___y_26_ = v___x_41_;
v___y_27_ = v_val_52_;
v___y_28_ = v_snd_40_;
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
v___y_23_ = v_val_44_;
v___y_24_ = v___x_61_;
v___y_25_ = v_val_47_;
v___y_26_ = v___x_41_;
v___y_27_ = v_val_52_;
v___y_28_ = v_snd_40_;
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
lean_object* v_val_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_210_; 
v_val_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_210_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_210_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_val_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_210_;
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
lean_object* v_val_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_205_; 
lean_del_object(v___x_169_);
v_val_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_205_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_205_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_val_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_205_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Syntax_getTailPos_x3f(v___x_172_, v___x_165_);
lean_dec(v___x_172_);
if (lean_obj_tag(v___x_178_) == 1)
{
lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_199_; 
lean_del_object(v___x_176_);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v___x_178_, 0);
lean_dec(v_unused_200_);
v___x_180_ = v___x_178_;
v_isShared_181_ = v_isSharedCheck_199_;
goto v_resetjp_179_;
}
else
{
lean_dec(v___x_178_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_199_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v_fileMap_182_; lean_object* v___x_183_; lean_object* v_line_184_; lean_object* v_character_185_; lean_object* v___x_186_; lean_object* v_line_187_; lean_object* v_character_188_; uint8_t v___x_189_; 
v_fileMap_182_ = lean_ctor_get(v_a_141_, 1);
lean_inc_ref_n(v_fileMap_182_, 2);
v___x_183_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_182_, v_val_167_);
lean_dec(v_val_167_);
v_line_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_line_184_);
v_character_185_ = lean_ctor_get(v___x_183_, 1);
lean_inc(v_character_185_);
lean_dec_ref(v___x_183_);
v___x_186_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_182_, v_val_174_);
lean_dec(v_val_174_);
v_line_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_line_187_);
v_character_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc(v_character_188_);
lean_dec_ref(v___x_186_);
v___x_189_ = lean_nat_dec_eq(v_line_187_, v_line_184_);
lean_dec(v_line_184_);
lean_dec(v_line_187_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_nat_dec_lt(v_character_188_, v_character_185_);
lean_dec(v_character_185_);
lean_dec(v_character_188_);
v___x_191_ = lean_box(v___x_190_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
lean_ctor_set(v___x_180_, 0, v___x_191_);
v___x_193_ = v___x_180_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_195_; lean_object* v___x_197_; 
lean_dec(v_character_188_);
lean_dec(v_character_185_);
v___x_195_ = lean_box(v___x_145_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 0);
lean_ctor_set(v___x_180_, 0, v___x_195_);
v___x_197_ = v___x_180_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec(v___x_178_);
lean_dec(v_val_174_);
lean_dec(v_val_167_);
v___x_201_ = lean_box(v___x_165_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
lean_ctor_set(v___x_176_, 0, v___x_201_);
v___x_203_ = v___x_176_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_208_; 
lean_dec(v___x_173_);
lean_dec(v___x_172_);
lean_dec(v_val_167_);
v___x_206_ = lean_box(v___x_165_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 0);
lean_ctor_set(v___x_169_, 0, v___x_206_);
v___x_208_ = v___x_169_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v___x_166_);
lean_dec(v_lastInterveningSepIdx_156_);
lean_dec(v_rawFields_150_);
v___x_211_ = lean_box(v___x_165_);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg___boxed(lean_object* v_stx_213_, lean_object* v_view_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_213_, v_view_214_, v_a_215_);
lean_dec_ref(v_a_215_);
lean_dec_ref(v_view_214_);
lean_dec(v_stx_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(lean_object* v_stx_218_, lean_object* v_view_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_218_, v_view_219_, v_a_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___boxed(lean_object* v_stx_226_, lean_object* v_view_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle(v_stx_226_, v_view_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec_ref(v_view_227_);
lean_dec(v_stx_226_);
return v_res_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object* v_opts_234_, lean_object* v_opt_235_){
_start:
{
lean_object* v_name_236_; lean_object* v_defValue_237_; lean_object* v_map_238_; lean_object* v___x_239_; 
v_name_236_ = lean_ctor_get(v_opt_235_, 0);
v_defValue_237_ = lean_ctor_get(v_opt_235_, 1);
v_map_238_ = lean_ctor_get(v_opts_234_, 0);
v___x_239_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_238_, v_name_236_);
if (lean_obj_tag(v___x_239_) == 0)
{
uint8_t v___x_240_; 
v___x_240_ = lean_unbox(v_defValue_237_);
return v___x_240_;
}
else
{
lean_object* v_val_241_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_239_, 1);
if (lean_obj_tag(v_val_241_) == 1)
{
uint8_t v_v_242_; 
v_v_242_ = lean_ctor_get_uint8(v_val_241_, 0);
lean_dec_ref_known(v_val_241_, 0);
return v_v_242_;
}
else
{
uint8_t v___x_243_; 
lean_dec(v_val_241_);
v___x_243_ = lean_unbox(v_defValue_237_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object* v_opts_244_, lean_object* v_opt_245_){
_start:
{
uint8_t v_res_246_; lean_object* v_r_247_; 
v_res_246_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_244_, v_opt_245_);
lean_dec_ref(v_opt_245_);
lean_dec_ref(v_opts_244_);
v_r_247_ = lean_box(v_res_246_);
return v_r_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(lean_object* v_opts_248_, lean_object* v_opt_249_){
_start:
{
lean_object* v_name_250_; lean_object* v_defValue_251_; lean_object* v_map_252_; lean_object* v___x_253_; 
v_name_250_ = lean_ctor_get(v_opt_249_, 0);
v_defValue_251_ = lean_ctor_get(v_opt_249_, 1);
v_map_252_ = lean_ctor_get(v_opts_248_, 0);
v___x_253_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_252_, v_name_250_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_inc(v_defValue_251_);
return v_defValue_251_;
}
else
{
lean_object* v_val_254_; 
v_val_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v___x_253_, 1);
if (lean_obj_tag(v_val_254_) == 3)
{
lean_object* v_v_255_; 
v_v_255_ = lean_ctor_get(v_val_254_, 0);
lean_inc(v_v_255_);
lean_dec_ref_known(v_val_254_, 1);
return v_v_255_;
}
else
{
lean_dec(v_val_254_);
lean_inc(v_defValue_251_);
return v_defValue_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object* v_opts_256_, lean_object* v_opt_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_opts_256_, v_opt_257_);
lean_dec_ref(v_opt_257_);
lean_dec_ref(v_opts_256_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object* v_msg_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = l_String_instInhabitedSlice;
v___x_261_ = lean_panic_fn_borrowed(v___x_260_, v_msg_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object* v_x_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0));
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(v_x_265_);
lean_dec_ref(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object* v_fileMap_267_, lean_object* v_p_268_){
_start:
{
lean_object* v___x_269_; lean_object* v_character_270_; 
v___x_269_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_267_, v_p_268_);
v_character_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_character_270_);
lean_dec_ref(v___x_269_);
return v_character_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object* v_fileMap_271_, lean_object* v_p_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_271_, v_p_272_);
lean_dec(v_p_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_dec(v_x_274_);
return v_x_275_;
}
else
{
lean_object* v_head_277_; lean_object* v_tail_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_288_; 
v_head_277_ = lean_ctor_get(v_x_276_, 0);
v_tail_278_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_288_ == 0)
{
v___x_280_ = v_x_276_;
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_tail_278_);
lean_inc(v_head_277_);
lean_dec(v_x_276_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_288_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
lean_inc(v_x_274_);
if (v_isShared_281_ == 0)
{
lean_ctor_set_tag(v___x_280_, 5);
lean_ctor_set(v___x_280_, 1, v_x_274_);
lean_ctor_set(v___x_280_, 0, v_x_275_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_x_275_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_x_274_);
v___x_283_ = v_reuseFailAlloc_287_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v_head_277_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v_x_275_ = v___x_285_;
v_x_276_ = v_tail_278_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_289_) == 0)
{
lean_object* v___x_291_; 
lean_dec(v_x_290_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
else
{
lean_object* v_tail_292_; 
v_tail_292_ = lean_ctor_get(v_x_289_, 1);
if (lean_obj_tag(v_tail_292_) == 0)
{
lean_object* v_head_293_; lean_object* v___x_294_; 
lean_dec(v_x_290_);
v_head_293_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_head_293_);
lean_dec_ref_known(v_x_289_, 2);
v___x_294_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_294_, 0, v_head_293_);
return v___x_294_;
}
else
{
lean_object* v_head_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_inc(v_tail_292_);
v_head_295_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_head_295_);
lean_dec_ref_known(v_x_289_, 2);
v___x_296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_296_, 0, v_head_295_);
v___x_297_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(v_x_290_, v___x_296_, v_tail_292_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(lean_object* v___x_298_, lean_object* v_j_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_zero_301_; uint8_t v_isZero_302_; 
v_zero_301_ = lean_unsigned_to_nat(0u);
v_isZero_302_ = lean_nat_dec_eq(v_j_299_, v_zero_301_);
if (v_isZero_302_ == 1)
{
lean_dec(v_j_299_);
return v_a_300_;
}
else
{
lean_object* v_one_303_; lean_object* v_n_304_; lean_object* v___x_305_; 
v_one_303_ = lean_unsigned_to_nat(1u);
v_n_304_ = lean_nat_sub(v_j_299_, v_one_303_);
lean_dec(v_j_299_);
v___x_305_ = lean_string_utf8_next(v___x_298_, v_a_300_);
lean_dec(v_a_300_);
v_j_299_ = v_n_304_;
v_a_300_ = v___x_305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg___boxed(lean_object* v___x_307_, lean_object* v_j_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_307_, v_j_308_, v_a_309_);
lean_dec_ref(v___x_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(lean_object* v_o_314_, lean_object* v_k_315_, uint8_t v_v_316_){
_start:
{
lean_object* v_map_317_; uint8_t v_hasTrace_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_332_; 
v_map_317_ = lean_ctor_get(v_o_314_, 0);
v_hasTrace_318_ = lean_ctor_get_uint8(v_o_314_, sizeof(void*)*1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_o_314_);
if (v_isSharedCheck_332_ == 0)
{
v___x_320_ = v_o_314_;
v_isShared_321_ = v_isSharedCheck_332_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_map_317_);
lean_dec(v_o_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_332_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_322_, 0, v_v_316_);
lean_inc(v_k_315_);
v___x_323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_315_, v___x_322_, v_map_317_);
if (v_hasTrace_318_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1));
v___x_325_ = l_Lean_Name_isPrefixOf(v___x_324_, v_k_315_);
lean_dec(v_k_315_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_323_);
v___x_327_ = v___x_320_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_323_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_325_);
return v___x_327_;
}
}
else
{
lean_object* v___x_330_; 
lean_dec(v_k_315_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_323_);
v___x_330_ = v___x_320_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_323_);
lean_ctor_set_uint8(v_reuseFailAlloc_331_, sizeof(void*)*1, v_hasTrace_318_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(lean_object* v_o_333_, lean_object* v_k_334_, lean_object* v_v_335_){
_start:
{
uint8_t v_v_boxed_336_; lean_object* v_res_337_; 
v_v_boxed_336_ = lean_unbox(v_v_335_);
v_res_337_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_o_333_, v_k_334_, v_v_boxed_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object* v_opts_338_, lean_object* v_opt_339_, uint8_t v_val_340_){
_start:
{
lean_object* v_name_341_; lean_object* v___x_342_; 
v_name_341_ = lean_ctor_get(v_opt_339_, 0);
lean_inc(v_name_341_);
lean_dec_ref(v_opt_339_);
v___x_342_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_opts_338_, v_name_341_, v_val_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object* v_opts_343_, lean_object* v_opt_344_, lean_object* v_val_345_){
_start:
{
uint8_t v_val_boxed_346_; lean_object* v_res_347_; 
v_val_boxed_346_ = lean_unbox(v_val_345_);
v_res_347_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_opts_343_, v_opt_344_, v_val_boxed_346_);
return v_res_347_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3(void){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_352_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4);
v___x_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(size_t v_sz_358_, size_t v_i_359_, lean_object* v_bs_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_lt(v_i_359_, v_sz_358_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_bs_360_);
return v___x_367_;
}
else
{
lean_object* v_v_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; lean_object* v_bs_x27_372_; lean_object* v_value_374_; 
v_v_368_ = lean_array_uget_borrowed(v_bs_360_, v_i_359_);
v_fst_369_ = lean_ctor_get(v_v_368_, 0);
lean_inc(v_fst_369_);
v_snd_370_ = lean_ctor_get(v_v_368_, 1);
lean_inc(v_snd_370_);
v___x_371_ = lean_unsigned_to_nat(0u);
v_bs_x27_372_ = lean_array_uset(v_bs_360_, v_i_359_, v___x_371_);
if (lean_obj_tag(v_snd_370_) == 1)
{
lean_object* v_val_383_; lean_object* v___x_384_; lean_object* v_fileName_385_; lean_object* v_fileMap_386_; lean_object* v_options_387_; lean_object* v_currRecDepth_388_; lean_object* v_ref_389_; lean_object* v_currNamespace_390_; lean_object* v_openDecls_391_; lean_object* v_initHeartbeats_392_; lean_object* v_maxHeartbeats_393_; lean_object* v_quotContext_394_; lean_object* v_currMacroScope_395_; lean_object* v_cancelTk_x3f_396_; uint8_t v_suppressElabErrors_397_; lean_object* v_inheritedTraceOptions_398_; lean_object* v_env_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; lean_object* v_fileName_407_; lean_object* v_fileMap_408_; lean_object* v_currRecDepth_409_; lean_object* v_ref_410_; lean_object* v_currNamespace_411_; lean_object* v_openDecls_412_; lean_object* v_initHeartbeats_413_; lean_object* v_maxHeartbeats_414_; lean_object* v_quotContext_415_; lean_object* v_currMacroScope_416_; lean_object* v_cancelTk_x3f_417_; uint8_t v_suppressElabErrors_418_; lean_object* v_inheritedTraceOptions_419_; lean_object* v___y_420_; uint8_t v___y_448_; uint8_t v___x_469_; 
v_val_383_ = lean_ctor_get(v_snd_370_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_snd_370_, 1);
v___x_384_ = lean_st_ref_get(v___y_364_);
v_fileName_385_ = lean_ctor_get(v___y_363_, 0);
v_fileMap_386_ = lean_ctor_get(v___y_363_, 1);
v_options_387_ = lean_ctor_get(v___y_363_, 2);
v_currRecDepth_388_ = lean_ctor_get(v___y_363_, 3);
v_ref_389_ = lean_ctor_get(v___y_363_, 5);
v_currNamespace_390_ = lean_ctor_get(v___y_363_, 6);
v_openDecls_391_ = lean_ctor_get(v___y_363_, 7);
v_initHeartbeats_392_ = lean_ctor_get(v___y_363_, 8);
v_maxHeartbeats_393_ = lean_ctor_get(v___y_363_, 9);
v_quotContext_394_ = lean_ctor_get(v___y_363_, 10);
v_currMacroScope_395_ = lean_ctor_get(v___y_363_, 11);
v_cancelTk_x3f_396_ = lean_ctor_get(v___y_363_, 12);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_363_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_398_ = lean_ctor_get(v___y_363_, 13);
v_env_399_ = lean_ctor_get(v___x_384_, 0);
lean_inc_ref(v_env_399_);
lean_dec(v___x_384_);
v___x_400_ = lean_box(1);
v___x_401_ = l_Lean_pp_mvars;
v___x_402_ = 0;
lean_inc_ref(v_options_387_);
v___x_403_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_options_387_, v___x_401_, v___x_402_);
v___x_404_ = l_Lean_diagnostics;
v___x_405_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v___x_403_, v___x_404_);
v___x_469_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_399_);
lean_dec_ref(v_env_399_);
if (v___x_405_ == 0)
{
if (v___x_469_ == 0)
{
v___y_448_ = v___x_366_;
goto v___jp_447_;
}
else
{
v___y_448_ = v___x_405_;
goto v___jp_447_;
}
}
else
{
v___y_448_ = v___x_469_;
goto v___jp_447_;
}
v___jp_406_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = l_Lean_maxRecDepth;
v___x_422_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___x_403_, v___x_421_);
lean_inc_ref(v_inheritedTraceOptions_419_);
lean_inc(v_cancelTk_x3f_417_);
lean_inc(v_currMacroScope_416_);
lean_inc(v_quotContext_415_);
lean_inc(v_maxHeartbeats_414_);
lean_inc(v_initHeartbeats_413_);
lean_inc(v_openDecls_412_);
lean_inc(v_currNamespace_411_);
lean_inc(v_ref_410_);
lean_inc(v_currRecDepth_409_);
lean_inc_ref(v_fileMap_408_);
lean_inc_ref(v_fileName_407_);
v___x_423_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_423_, 0, v_fileName_407_);
lean_ctor_set(v___x_423_, 1, v_fileMap_408_);
lean_ctor_set(v___x_423_, 2, v___x_403_);
lean_ctor_set(v___x_423_, 3, v_currRecDepth_409_);
lean_ctor_set(v___x_423_, 4, v___x_422_);
lean_ctor_set(v___x_423_, 5, v_ref_410_);
lean_ctor_set(v___x_423_, 6, v_currNamespace_411_);
lean_ctor_set(v___x_423_, 7, v_openDecls_412_);
lean_ctor_set(v___x_423_, 8, v_initHeartbeats_413_);
lean_ctor_set(v___x_423_, 9, v_maxHeartbeats_414_);
lean_ctor_set(v___x_423_, 10, v_quotContext_415_);
lean_ctor_set(v___x_423_, 11, v_currMacroScope_416_);
lean_ctor_set(v___x_423_, 12, v_cancelTk_x3f_417_);
lean_ctor_set(v___x_423_, 13, v_inheritedTraceOptions_419_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14, v___x_405_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*14 + 1, v_suppressElabErrors_418_);
v___x_424_ = l_Lean_PrettyPrinter_delab(v_val_383_, v___x_400_, v___y_361_, v___y_362_, v___x_423_, v___y_420_);
lean_dec_ref_known(v___x_423_, 14);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2));
v___x_427_ = l_Lean_PrettyPrinter_ppCategory(v___x_426_, v_a_425_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = l_Std_Format_defWidth;
v___x_430_ = l_Std_Format_pretty(v_a_428_, v___x_429_, v___x_371_, v___x_371_);
v_value_374_ = v___x_430_;
goto v___jp_373_;
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref(v_bs_x27_372_);
lean_dec(v_fst_369_);
v_a_431_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_427_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_bs_x27_372_);
lean_dec(v_fst_369_);
v_a_439_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_424_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_424_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
v___jp_447_:
{
if (v___y_448_ == 0)
{
lean_object* v___x_449_; lean_object* v_env_450_; lean_object* v_nextMacroScope_451_; lean_object* v_ngen_452_; lean_object* v_auxDeclNGen_453_; lean_object* v_traceState_454_; lean_object* v_messages_455_; lean_object* v_infoState_456_; lean_object* v_snapshotTasks_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_467_; 
v___x_449_ = lean_st_ref_take(v___y_364_);
v_env_450_ = lean_ctor_get(v___x_449_, 0);
v_nextMacroScope_451_ = lean_ctor_get(v___x_449_, 1);
v_ngen_452_ = lean_ctor_get(v___x_449_, 2);
v_auxDeclNGen_453_ = lean_ctor_get(v___x_449_, 3);
v_traceState_454_ = lean_ctor_get(v___x_449_, 4);
v_messages_455_ = lean_ctor_get(v___x_449_, 6);
v_infoState_456_ = lean_ctor_get(v___x_449_, 7);
v_snapshotTasks_457_ = lean_ctor_get(v___x_449_, 8);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_449_, 5);
lean_dec(v_unused_468_);
v___x_459_ = v___x_449_;
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snapshotTasks_457_);
lean_inc(v_infoState_456_);
lean_inc(v_messages_455_);
lean_inc(v_traceState_454_);
lean_inc(v_auxDeclNGen_453_);
lean_inc(v_ngen_452_);
lean_inc(v_nextMacroScope_451_);
lean_inc(v_env_450_);
lean_dec(v___x_449_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_467_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = l_Lean_Kernel_enableDiag(v_env_450_, v___x_405_);
v___x_462_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 5, v___x_462_);
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_nextMacroScope_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_ngen_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_auxDeclNGen_453_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_traceState_454_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_messages_455_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_infoState_456_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_snapshotTasks_457_);
v___x_464_ = v_reuseFailAlloc_466_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; 
v___x_465_ = lean_st_ref_put(v___y_364_, v___x_464_);
v_fileName_407_ = v_fileName_385_;
v_fileMap_408_ = v_fileMap_386_;
v_currRecDepth_409_ = v_currRecDepth_388_;
v_ref_410_ = v_ref_389_;
v_currNamespace_411_ = v_currNamespace_390_;
v_openDecls_412_ = v_openDecls_391_;
v_initHeartbeats_413_ = v_initHeartbeats_392_;
v_maxHeartbeats_414_ = v_maxHeartbeats_393_;
v_quotContext_415_ = v_quotContext_394_;
v_currMacroScope_416_ = v_currMacroScope_395_;
v_cancelTk_x3f_417_ = v_cancelTk_x3f_396_;
v_suppressElabErrors_418_ = v_suppressElabErrors_397_;
v_inheritedTraceOptions_419_ = v_inheritedTraceOptions_398_;
v___y_420_ = v___y_364_;
goto v___jp_406_;
}
}
}
else
{
v_fileName_407_ = v_fileName_385_;
v_fileMap_408_ = v_fileMap_386_;
v_currRecDepth_409_ = v_currRecDepth_388_;
v_ref_410_ = v_ref_389_;
v_currNamespace_411_ = v_currNamespace_390_;
v_openDecls_412_ = v_openDecls_391_;
v_initHeartbeats_413_ = v_initHeartbeats_392_;
v_maxHeartbeats_414_ = v_maxHeartbeats_393_;
v_quotContext_415_ = v_quotContext_394_;
v_currMacroScope_416_ = v_currMacroScope_395_;
v_cancelTk_x3f_417_ = v_cancelTk_x3f_396_;
v_suppressElabErrors_418_ = v_suppressElabErrors_397_;
v_inheritedTraceOptions_419_ = v_inheritedTraceOptions_398_;
v___y_420_ = v___y_364_;
goto v___jp_406_;
}
}
}
else
{
lean_object* v___x_470_; 
lean_dec(v_snd_370_);
v___x_470_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6));
v_value_374_ = v___x_470_;
goto v___jp_373_;
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; 
v___x_375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_369_, v___x_366_);
v___x_376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0));
v___x_377_ = lean_string_append(v___x_375_, v___x_376_);
v___x_378_ = lean_string_append(v___x_377_, v_value_374_);
lean_dec_ref(v_value_374_);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_i_359_, v___x_379_);
v___x_381_ = lean_array_uset(v_bs_x27_372_, v_i_359_, v___x_378_);
v_i_359_ = v___x_380_;
v_bs_360_ = v___x_381_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object* v_sz_471_, lean_object* v_i_472_, lean_object* v_bs_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_471_);
lean_dec(v_sz_471_);
v_i_boxed_480_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_boxed_479_, v_i_boxed_480_, v_bs_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object* v_s_482_, lean_object* v_pos_483_){
_start:
{
lean_object* v_str_484_; lean_object* v_startInclusive_485_; lean_object* v_endExclusive_486_; lean_object* v___x_487_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v_decide_498_; 
v_str_484_ = lean_ctor_get(v_s_482_, 0);
v_startInclusive_485_ = lean_ctor_get(v_s_482_, 1);
v_endExclusive_486_ = lean_ctor_get(v_s_482_, 2);
v___x_487_ = lean_nat_add(v_startInclusive_485_, v_pos_483_);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_nat_sub(v_endExclusive_486_, v___x_487_);
v_decide_498_ = lean_nat_dec_eq(v___x_496_, v___x_497_);
lean_dec(v___x_497_);
if (v_decide_498_ == 0)
{
uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = lean_string_utf8_get_fast(v_str_484_, v___x_487_);
v___x_500_ = 32;
v___x_501_ = lean_uint32_dec_eq(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_502_ = 9;
v___x_503_ = lean_uint32_dec_eq(v___x_499_, v___x_502_);
if (v___x_503_ == 0)
{
uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_504_ = 13;
v___x_505_ = lean_uint32_dec_eq(v___x_499_, v___x_504_);
if (v___x_505_ == 0)
{
uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 10;
v___x_507_ = lean_uint32_dec_eq(v___x_499_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v___x_487_);
return v_pos_483_;
}
else
{
goto v___jp_488_;
}
}
else
{
goto v___jp_488_;
}
}
else
{
goto v___jp_488_;
}
}
else
{
goto v___jp_488_;
}
}
else
{
lean_dec(v___x_487_);
return v_pos_483_;
}
v___jp_488_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_489_ = lean_string_utf8_next_fast(v_str_484_, v___x_487_);
v___x_490_ = lean_nat_sub(v___x_489_, v___x_487_);
lean_dec(v___x_487_);
v___x_491_ = lean_nat_add(v_pos_483_, v___x_490_);
lean_dec(v___x_490_);
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_pos_483_, v___x_492_);
v___x_494_ = lean_nat_dec_le(v___x_493_, v___x_491_);
lean_dec(v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v___x_491_);
return v_pos_483_;
}
else
{
lean_dec(v_pos_483_);
v_pos_483_ = v___x_491_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5___boxed(lean_object* v_s_508_, lean_object* v_pos_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v_s_508_, v_pos_509_);
lean_dec_ref(v_s_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(lean_object* v_as_513_, size_t v_i_514_, size_t v_stop_515_, lean_object* v_b_516_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_eq(v_i_514_, v_stop_515_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; size_t v___x_525_; size_t v___x_526_; 
v___x_518_ = lean_array_uget_borrowed(v_as_513_, v_i_514_);
v___x_519_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0));
v___x_520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_520_, 0, v_b_516_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_box(1);
v___x_522_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
lean_inc(v___x_518_);
v___x_523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_518_);
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_514_, v___x_525_);
v_i_514_ = v___x_526_;
v_b_516_ = v___x_524_;
goto _start;
}
else
{
return v_b_516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___boxed(lean_object* v_as_528_, lean_object* v_i_529_, lean_object* v_stop_530_, lean_object* v_b_531_){
_start:
{
size_t v_i_boxed_532_; size_t v_stop_boxed_533_; lean_object* v_res_534_; 
v_i_boxed_532_ = lean_unbox_usize(v_i_529_);
lean_dec(v_i_529_);
v_stop_boxed_533_ = lean_unbox_usize(v_stop_530_);
lean_dec(v_stop_530_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_as_528_, v_i_boxed_532_, v_stop_boxed_533_, v_b_531_);
lean_dec_ref(v_as_528_);
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
lean_object* v_val_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_806_; 
v_val_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_806_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_806_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_val_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_806_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v_sz_567_; size_t v___x_568_; lean_object* v___x_569_; 
v_sz_567_ = lean_array_size(v_fields_555_);
v___x_568_ = ((size_t)0ULL);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_567_, v___x_568_, v_fields_555_, v_a_557_, v_a_558_, v_a_559_, v_a_560_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_797_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_556_, v_val_563_, v_a_559_);
lean_dec(v_stx_556_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_797_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_797_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_797_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
uint8_t v___x_576_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v_fst_614_; lean_object* v_snd_615_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_649_; uint8_t v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; uint8_t v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_665_; uint8_t v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_677_; lean_object* v___y_678_; uint8_t v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v_startInclusive_689_; lean_object* v_endExclusive_690_; lean_object* v___y_698_; lean_object* v___y_699_; uint8_t v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_714_; uint8_t v___y_715_; uint8_t v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; uint8_t v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; uint8_t v___y_727_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_768_; lean_object* v___y_781_; uint8_t v___x_784_; 
v___x_576_ = 1;
v___x_784_ = lean_unbox(v_a_572_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_array_to_list(v_a_570_);
v___x_786_ = lean_box(1);
v___x_787_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v___x_785_, v___x_786_);
v___y_768_ = v___x_787_;
goto v___jp_767_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_788_ = lean_box(0);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_array_get_size(v_a_570_);
v___x_791_ = lean_nat_dec_lt(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec(v_a_570_);
v___y_781_ = v___x_788_;
goto v___jp_780_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = lean_nat_dec_le(v___x_790_, v___x_790_);
if (v___x_792_ == 0)
{
if (v___x_791_ == 0)
{
lean_dec(v_a_570_);
v___y_781_ = v___x_788_;
goto v___jp_780_;
}
else
{
size_t v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_usize_of_nat(v___x_790_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_570_, v___x_568_, v___x_793_, v___x_788_);
lean_dec(v_a_570_);
v___y_781_ = v___x_794_;
goto v___jp_780_;
}
}
else
{
size_t v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_usize_of_nat(v___x_790_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_570_, v___x_568_, v___x_795_, v___x_788_);
lean_dec(v_a_570_);
v___y_781_ = v___x_796_;
goto v___jp_780_;
}
}
}
v___jp_577_:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_583_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_584_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___y_581_, v___x_583_);
lean_inc(v___y_582_);
v___x_585_ = lean_apply_1(v___y_579_, v___y_582_);
v___x_586_ = l_Std_Format_pretty(v___y_580_, v___x_584_, v___y_578_, v___x_585_);
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
lean_inc(v___y_582_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___y_582_);
lean_ctor_set(v___x_592_, 1, v___y_582_);
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
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v_fst_614_);
lean_ctor_set(v___x_616_, 1, v___y_611_);
v___x_617_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v_snd_615_);
if (lean_obj_tag(v___y_613_) == 0)
{
if (lean_obj_tag(v___y_608_) == 0)
{
v___y_578_ = v___y_609_;
v___y_579_ = v___y_610_;
v___y_580_ = v___x_617_;
v___y_581_ = v___y_612_;
v___y_582_ = v___y_607_;
goto v___jp_577_;
}
else
{
lean_object* v_val_618_; 
lean_dec(v___y_607_);
v_val_618_ = lean_ctor_get(v___y_608_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v___y_608_, 1);
v___y_578_ = v___y_609_;
v___y_579_ = v___y_610_;
v___y_580_ = v___x_617_;
v___y_581_ = v___y_612_;
v___y_582_ = v_val_618_;
goto v___jp_577_;
}
}
else
{
lean_object* v_val_619_; 
lean_dec(v___y_608_);
lean_dec(v___y_607_);
v_val_619_ = lean_ctor_get(v___y_613_, 0);
lean_inc(v_val_619_);
lean_dec_ref_known(v___y_613_, 1);
v___y_578_ = v___y_609_;
v___y_579_ = v___y_610_;
v___y_580_ = v___x_617_;
v___y_581_ = v___y_612_;
v___y_582_ = v_val_619_;
goto v___jp_577_;
}
}
v___jp_620_:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_box(1);
v___x_629_ = lean_box(0);
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_623_;
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v_fst_614_ = v___x_628_;
v_snd_615_ = v___x_629_;
goto v___jp_606_;
}
v___jp_630_:
{
if (lean_obj_tag(v___y_632_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_box(1);
v___x_639_ = lean_box(0);
v___y_607_ = v___y_631_;
v___y_608_ = v___y_632_;
v___y_609_ = v___y_633_;
v___y_610_ = v___y_634_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_636_;
v___y_613_ = v___y_637_;
v_fst_614_ = v___x_638_;
v_snd_615_ = v___x_639_;
goto v___jp_606_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_val_640_ = lean_ctor_get(v___y_632_, 0);
lean_inc_ref(v___y_634_);
lean_inc(v_val_640_);
v___x_641_ = lean_apply_1(v___y_634_, v_val_640_);
v___x_642_ = lean_nat_sub(v___y_633_, v___x_641_);
lean_dec(v___x_641_);
v___x_643_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
v___x_644_ = l_List_replicateTR___redArg(v___x_642_, v___x_643_);
v___x_645_ = lean_string_mk(v___x_644_);
v___x_646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_box(0);
v___y_607_ = v___y_631_;
v___y_608_ = v___y_632_;
v___y_609_ = v___y_633_;
v___y_610_ = v___y_634_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_636_;
v___y_613_ = v___y_637_;
v_fst_614_ = v___x_646_;
v_snd_615_ = v___x_647_;
goto v___jp_606_;
}
}
v___jp_648_:
{
uint8_t v___x_659_; 
v___x_659_ = lean_unbox(v_a_572_);
lean_dec(v_a_572_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_nat_dec_lt(v___x_660_, v___y_654_);
lean_dec(v___y_654_);
if (v___x_661_ == 0)
{
if (v___y_653_ == 0)
{
if (v___y_650_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5));
v___y_607_ = v___y_649_;
v___y_608_ = v___y_658_;
v___y_609_ = v___y_651_;
v___y_610_ = v___y_652_;
v___y_611_ = v___y_655_;
v___y_612_ = v___y_656_;
v___y_613_ = v___y_657_;
v_fst_614_ = v___x_662_;
v_snd_615_ = v___x_662_;
goto v___jp_606_;
}
else
{
v___y_631_ = v___y_649_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_651_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_655_;
v___y_636_ = v___y_656_;
v___y_637_ = v___y_657_;
goto v___jp_630_;
}
}
else
{
if (v___y_650_ == 0)
{
v___y_621_ = v___y_649_;
v___y_622_ = v___y_658_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_655_;
v___y_626_ = v___y_656_;
v___y_627_ = v___y_657_;
goto v___jp_620_;
}
else
{
v___y_631_ = v___y_649_;
v___y_632_ = v___y_658_;
v___y_633_ = v___y_651_;
v___y_634_ = v___y_652_;
v___y_635_ = v___y_655_;
v___y_636_ = v___y_656_;
v___y_637_ = v___y_657_;
goto v___jp_630_;
}
}
}
else
{
v___y_621_ = v___y_649_;
v___y_622_ = v___y_658_;
v___y_623_ = v___y_651_;
v___y_624_ = v___y_652_;
v___y_625_ = v___y_655_;
v___y_626_ = v___y_656_;
v___y_627_ = v___y_657_;
goto v___jp_620_;
}
}
else
{
lean_object* v___x_663_; 
lean_dec(v___y_654_);
v___x_663_ = lean_box(0);
v___y_607_ = v___y_649_;
v___y_608_ = v___y_658_;
v___y_609_ = v___y_651_;
v___y_610_ = v___y_652_;
v___y_611_ = v___y_655_;
v___y_612_ = v___y_656_;
v___y_613_ = v___y_657_;
v_fst_614_ = v___x_663_;
v_snd_615_ = v___x_663_;
goto v___jp_606_;
}
}
v___jp_664_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v___y_674_);
v___y_649_ = v___y_665_;
v___y_650_ = v___y_666_;
v___y_651_ = v___y_667_;
v___y_652_ = v___y_668_;
v___y_653_ = v___y_669_;
v___y_654_ = v___y_670_;
v___y_655_ = v___y_671_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_673_;
v___y_658_ = v___x_675_;
goto v___jp_648_;
}
v___jp_676_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v_decide_694_; 
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___y_688_, v___x_691_);
lean_dec_ref(v___y_688_);
v___x_693_ = lean_nat_sub(v_endExclusive_690_, v_startInclusive_689_);
lean_dec(v_startInclusive_689_);
lean_dec(v_endExclusive_690_);
v_decide_694_ = lean_nat_dec_eq(v___x_692_, v___x_693_);
lean_dec(v___x_693_);
lean_dec(v___x_692_);
if (v_decide_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec(v___y_686_);
lean_dec(v___y_677_);
v___x_695_ = lean_box(0);
v___y_649_ = v___y_678_;
v___y_650_ = v___y_679_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
v___y_656_ = v___y_685_;
v___y_657_ = v___y_687_;
v___y_658_ = v___x_695_;
goto v___jp_648_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = lean_nat_dec_le(v___y_686_, v___y_677_);
if (v___x_696_ == 0)
{
lean_dec(v___y_686_);
v___y_665_ = v___y_678_;
v___y_666_ = v___y_679_;
v___y_667_ = v___y_680_;
v___y_668_ = v___y_681_;
v___y_669_ = v___y_682_;
v___y_670_ = v___y_683_;
v___y_671_ = v___y_684_;
v___y_672_ = v___y_685_;
v___y_673_ = v___y_687_;
v___y_674_ = v___y_677_;
goto v___jp_664_;
}
else
{
lean_dec(v___y_677_);
v___y_665_ = v___y_678_;
v___y_666_ = v___y_679_;
v___y_667_ = v___y_680_;
v___y_668_ = v___y_681_;
v___y_669_ = v___y_682_;
v___y_670_ = v___y_683_;
v___y_671_ = v___y_684_;
v___y_672_ = v___y_685_;
v___y_673_ = v___y_687_;
v___y_674_ = v___y_686_;
goto v___jp_664_;
}
}
}
v___jp_697_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_startInclusive_711_; lean_object* v_endExclusive_712_; 
v___x_709_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9);
v___x_710_ = l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(v___x_709_);
v_startInclusive_711_ = lean_ctor_get(v___x_710_, 1);
lean_inc(v_startInclusive_711_);
v_endExclusive_712_ = lean_ctor_get(v___x_710_, 2);
lean_inc(v_endExclusive_712_);
v___y_677_ = v___y_699_;
v___y_678_ = v___y_698_;
v___y_679_ = v___y_700_;
v___y_680_ = v___y_701_;
v___y_681_ = v___y_702_;
v___y_682_ = v___y_703_;
v___y_683_ = v___y_704_;
v___y_684_ = v___y_705_;
v___y_685_ = v___y_706_;
v___y_686_ = v___y_708_;
v___y_687_ = v___y_707_;
v___y_688_ = v___x_710_;
v_startInclusive_689_ = v_startInclusive_711_;
v_endExclusive_690_ = v_endExclusive_712_;
goto v___jp_676_;
}
v___jp_713_:
{
if (v___y_715_ == 0)
{
lean_dec_ref(v___y_714_);
v___y_698_ = v___y_719_;
v___y_699_ = v___y_720_;
v___y_700_ = v___y_716_;
v___y_701_ = v___y_721_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_723_;
v___y_704_ = v___y_717_;
v___y_705_ = v___y_724_;
v___y_706_ = v___y_725_;
v___y_707_ = v___y_726_;
v___y_708_ = v___y_718_;
goto v___jp_697_;
}
else
{
if (v___y_727_ == 0)
{
lean_dec_ref(v___y_714_);
v___y_698_ = v___y_719_;
v___y_699_ = v___y_720_;
v___y_700_ = v___y_716_;
v___y_701_ = v___y_721_;
v___y_702_ = v___y_722_;
v___y_703_ = v___y_723_;
v___y_704_ = v___y_717_;
v___y_705_ = v___y_724_;
v___y_706_ = v___y_725_;
v___y_707_ = v___y_726_;
v___y_708_ = v___y_718_;
goto v___jp_697_;
}
else
{
lean_object* v___x_728_; 
lean_inc_n(v___y_720_, 2);
lean_inc_n(v___y_719_, 2);
v___x_728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_728_, 0, v___y_714_);
lean_ctor_set(v___x_728_, 1, v___y_719_);
lean_ctor_set(v___x_728_, 2, v___y_720_);
v___y_677_ = v___y_720_;
v___y_678_ = v___y_719_;
v___y_679_ = v___y_716_;
v___y_680_ = v___y_721_;
v___y_681_ = v___y_722_;
v___y_682_ = v___y_723_;
v___y_683_ = v___y_717_;
v___y_684_ = v___y_724_;
v___y_685_ = v___y_725_;
v___y_686_ = v___y_718_;
v___y_687_ = v___y_726_;
v___y_688_ = v___x_728_;
v_startInclusive_689_ = v___y_719_;
v_endExclusive_690_ = v___y_720_;
goto v___jp_676_;
}
}
}
v___jp_729_:
{
lean_object* v_lastFieldTailPos_x3f_735_; uint8_t v_hasWith_736_; lean_object* v_numFields_737_; lean_object* v_leaderPos_738_; lean_object* v_leaderTailPos_739_; lean_object* v_closingPos_740_; lean_object* v___x_741_; lean_object* v_line_742_; lean_object* v___x_743_; lean_object* v_line_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_lastFieldTailPos_x3f_735_ = lean_ctor_get(v_val_563_, 1);
lean_inc(v_lastFieldTailPos_x3f_735_);
v_hasWith_736_ = lean_ctor_get_uint8(v_val_563_, sizeof(void*)*7);
v_numFields_737_ = lean_ctor_get(v_val_563_, 2);
lean_inc(v_numFields_737_);
v_leaderPos_738_ = lean_ctor_get(v_val_563_, 4);
lean_inc(v_leaderPos_738_);
v_leaderTailPos_739_ = lean_ctor_get(v_val_563_, 5);
lean_inc(v_leaderTailPos_739_);
v_closingPos_740_ = lean_ctor_get(v_val_563_, 6);
lean_inc(v_closingPos_740_);
lean_dec(v_val_563_);
lean_inc_ref_n(v___y_731_, 2);
v___x_741_ = l_Lean_FileMap_utf8PosToLspPos(v___y_731_, v_leaderPos_738_);
lean_dec(v_leaderPos_738_);
v_line_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_line_742_);
lean_dec_ref(v___x_741_);
v___x_743_ = l_Lean_FileMap_utf8PosToLspPos(v___y_731_, v_closingPos_740_);
lean_dec(v_closingPos_740_);
v_line_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_line_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = lean_nat_dec_lt(v_line_742_, v_line_744_);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_line_742_, v___x_746_);
lean_dec(v_line_742_);
v___x_748_ = lean_nat_dec_le(v_line_744_, v___x_747_);
lean_dec(v___x_747_);
lean_dec(v_line_744_);
if (v___x_748_ == 0)
{
lean_object* v_source_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; uint8_t v___x_756_; 
v_source_749_ = lean_ctor_get(v___y_731_, 0);
lean_inc_ref_n(v_source_749_, 3);
lean_dec_ref(v___y_731_);
v___x_750_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_749_, v_leaderTailPos_739_);
v___x_751_ = lean_nat_add(v___y_734_, v___x_746_);
lean_inc(v___x_750_);
v___x_752_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v_source_749_, v___x_751_, v___x_750_);
v___x_753_ = lean_string_utf8_next(v_source_749_, v___x_750_);
lean_dec(v___x_750_);
v___x_754_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_749_, v___x_753_);
lean_dec(v___x_753_);
v___x_755_ = lean_string_is_valid_pos(v_source_749_, v_leaderTailPos_739_);
v___x_756_ = lean_string_is_valid_pos(v_source_749_, v___x_754_);
if (v___x_756_ == 0)
{
v___y_714_ = v_source_749_;
v___y_715_ = v___x_755_;
v___y_716_ = v___x_745_;
v___y_717_ = v_numFields_737_;
v___y_718_ = v___x_752_;
v___y_719_ = v_leaderTailPos_739_;
v___y_720_ = v___x_754_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_730_;
v___y_723_ = v_hasWith_736_;
v___y_724_ = v___y_732_;
v___y_725_ = v___y_733_;
v___y_726_ = v_lastFieldTailPos_x3f_735_;
v___y_727_ = v___x_756_;
goto v___jp_713_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_le(v_leaderTailPos_739_, v___x_754_);
v___y_714_ = v_source_749_;
v___y_715_ = v___x_755_;
v___y_716_ = v___x_745_;
v___y_717_ = v_numFields_737_;
v___y_718_ = v___x_752_;
v___y_719_ = v_leaderTailPos_739_;
v___y_720_ = v___x_754_;
v___y_721_ = v___y_734_;
v___y_722_ = v___y_730_;
v___y_723_ = v_hasWith_736_;
v___y_724_ = v___y_732_;
v___y_725_ = v___y_733_;
v___y_726_ = v_lastFieldTailPos_x3f_735_;
v___y_727_ = v___x_757_;
goto v___jp_713_;
}
}
else
{
lean_object* v___x_758_; 
lean_dec_ref(v___y_731_);
v___x_758_ = lean_box(0);
v___y_649_ = v_leaderTailPos_739_;
v___y_650_ = v___x_745_;
v___y_651_ = v___y_734_;
v___y_652_ = v___y_730_;
v___y_653_ = v_hasWith_736_;
v___y_654_ = v_numFields_737_;
v___y_655_ = v___y_732_;
v___y_656_ = v___y_733_;
v___y_657_ = v_lastFieldTailPos_x3f_735_;
v___y_658_ = v___x_758_;
goto v___jp_648_;
}
}
v___jp_759_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(2u);
v___x_766_ = lean_nat_add(v___y_764_, v___x_765_);
lean_dec(v___y_764_);
v___y_730_ = v___y_760_;
v___y_731_ = v___y_761_;
v___y_732_ = v___y_762_;
v___y_733_ = v___y_763_;
v___y_734_ = v___x_766_;
goto v___jp_729_;
}
v___jp_767_:
{
lean_object* v_fileMap_769_; lean_object* v_options_770_; lean_object* v_initFieldPos_x3f_771_; lean_object* v_openingPos_772_; lean_object* v_closingPos_773_; lean_object* v___f_774_; 
v_fileMap_769_ = lean_ctor_get(v_a_559_, 1);
v_options_770_ = lean_ctor_get(v_a_559_, 2);
v_initFieldPos_x3f_771_ = lean_ctor_get(v_val_563_, 0);
v_openingPos_772_ = lean_ctor_get(v_val_563_, 3);
v_closingPos_773_ = lean_ctor_get(v_val_563_, 6);
lean_inc_ref(v_fileMap_769_);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed), 2, 1);
lean_closure_set(v___f_774_, 0, v_fileMap_769_);
if (lean_obj_tag(v_initFieldPos_x3f_771_) == 1)
{
lean_object* v_val_775_; lean_object* v___x_776_; 
v_val_775_ = lean_ctor_get(v_initFieldPos_x3f_771_, 0);
lean_inc_ref_n(v_fileMap_769_, 2);
v___x_776_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_769_, v_val_775_);
v___y_730_ = v___f_774_;
v___y_731_ = v_fileMap_769_;
v___y_732_ = v___y_768_;
v___y_733_ = v_options_770_;
v___y_734_ = v___x_776_;
goto v___jp_729_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
lean_inc_ref_n(v_fileMap_769_, 2);
v___x_777_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_769_, v_openingPos_772_);
v___x_778_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_769_, v_closingPos_773_);
v___x_779_ = lean_nat_dec_le(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_dec(v___x_777_);
lean_inc_ref(v_fileMap_769_);
v___y_760_ = v___f_774_;
v___y_761_ = v_fileMap_769_;
v___y_762_ = v___y_768_;
v___y_763_ = v_options_770_;
v___y_764_ = v___x_778_;
goto v___jp_759_;
}
else
{
lean_dec(v___x_778_);
lean_inc_ref(v_fileMap_769_);
v___y_760_ = v___f_774_;
v___y_761_ = v_fileMap_769_;
v___y_762_ = v___y_768_;
v___y_763_ = v_options_770_;
v___y_764_ = v___x_777_;
goto v___jp_759_;
}
}
}
v___jp_780_:
{
uint8_t v___x_782_; lean_object* v___x_783_; 
v___x_782_ = 1;
v___x_783_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_783_, 0, v___y_781_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v___x_782_);
v___y_768_ = v___x_783_;
goto v___jp_767_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_del_object(v___x_565_);
lean_dec(v_val_563_);
lean_dec(v_stx_556_);
v_a_798_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_569_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_569_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_562_);
lean_dec(v_stx_556_);
lean_dec_ref(v_fields_555_);
v___x_807_ = l_Lean_MessageData_nil;
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object* v_fields_809_, lean_object* v_stx_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_809_, v_stx_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object* v___x_817_, lean_object* v_n_818_, lean_object* v_j_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_817_, v_j_819_, v_a_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object* v___x_823_, lean_object* v_n_824_, lean_object* v_j_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___x_823_, v_n_824_, v_j_825_, v_a_826_, v_a_827_);
lean_dec(v_n_824_);
lean_dec_ref(v___x_823_);
return v_res_828_;
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
