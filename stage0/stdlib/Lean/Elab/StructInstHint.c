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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
lean_object* v_name_237_; lean_object* v_defValue_238_; lean_object* v_map_239_; lean_object* v___x_240_; 
v_name_237_ = lean_ctor_get(v_opt_236_, 0);
v_defValue_238_ = lean_ctor_get(v_opt_236_, 1);
v_map_239_ = lean_ctor_get(v_opts_235_, 0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_239_, v_name_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
uint8_t v___x_241_; 
v___x_241_ = lean_unbox(v_defValue_238_);
return v___x_241_;
}
else
{
lean_object* v_val_242_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v___x_240_, 1);
if (lean_obj_tag(v_val_242_) == 1)
{
uint8_t v_v_243_; 
v_v_243_ = lean_ctor_get_uint8(v_val_242_, 0);
lean_dec_ref_known(v_val_242_, 0);
return v_v_243_;
}
else
{
uint8_t v___x_244_; 
lean_dec(v_val_242_);
v___x_244_ = lean_unbox(v_defValue_238_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1___boxed(lean_object* v_opts_245_, lean_object* v_opt_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v_opts_245_, v_opt_246_);
lean_dec_ref(v_opt_246_);
lean_dec_ref(v_opts_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(lean_object* v_opts_249_, lean_object* v_opt_250_){
_start:
{
lean_object* v_name_251_; lean_object* v_defValue_252_; lean_object* v_map_253_; lean_object* v___x_254_; 
v_name_251_ = lean_ctor_get(v_opt_250_, 0);
v_defValue_252_ = lean_ctor_get(v_opt_250_, 1);
v_map_253_ = lean_ctor_get(v_opts_249_, 0);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_253_, v_name_251_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_inc(v_defValue_252_);
return v_defValue_252_;
}
else
{
lean_object* v_val_255_; 
v_val_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_val_255_);
lean_dec_ref_known(v___x_254_, 1);
if (lean_obj_tag(v_val_255_) == 3)
{
lean_object* v_v_256_; 
v_v_256_ = lean_ctor_get(v_val_255_, 0);
lean_inc(v_v_256_);
lean_dec_ref_known(v_val_255_, 1);
return v_v_256_;
}
else
{
lean_dec(v_val_255_);
lean_inc(v_defValue_252_);
return v_defValue_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2___boxed(lean_object* v_opts_257_, lean_object* v_opt_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v_opts_257_, v_opt_258_);
lean_dec_ref(v_opt_258_);
lean_dec_ref(v_opts_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(lean_object* v_msg_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = l_String_instInhabitedSlice;
v___x_262_ = lean_panic_fn_borrowed(v___x_261_, v_msg_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(lean_object* v_x_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___closed__0));
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0___boxed(lean_object* v_x_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__0(v_x_266_);
lean_dec_ref(v_x_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(lean_object* v_fileMap_268_, lean_object* v_p_269_){
_start:
{
lean_object* v___x_270_; lean_object* v_character_271_; 
v___x_270_ = l_Lean_FileMap_utf8PosToLspPos(v_fileMap_268_, v_p_269_);
v_character_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_character_271_);
lean_dec_ref(v___x_270_);
return v_character_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed(lean_object* v_fileMap_272_, lean_object* v_p_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_272_, v_p_273_);
lean_dec(v_p_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_dec(v_x_275_);
return v_x_276_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_head_278_ = lean_ctor_get(v_x_277_, 0);
v_tail_279_ = lean_ctor_get(v_x_277_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_x_277_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v_x_277_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_tail_279_);
lean_inc(v_head_278_);
lean_dec(v_x_277_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
lean_inc(v_x_275_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 5);
lean_ctor_set(v___x_281_, 1, v_x_275_);
lean_ctor_set(v___x_281_, 0, v_x_276_);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_x_276_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_x_275_);
v___x_284_ = v_reuseFailAlloc_288_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_285_, 0, v_head_278_);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v_x_276_ = v___x_286_;
v_x_277_ = v_tail_279_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v___x_292_; 
lean_dec(v_x_291_);
v___x_292_ = lean_box(0);
return v___x_292_;
}
else
{
lean_object* v_tail_293_; 
v_tail_293_ = lean_ctor_get(v_x_290_, 1);
if (lean_obj_tag(v_tail_293_) == 0)
{
lean_object* v_head_294_; lean_object* v___x_295_; 
lean_dec(v_x_291_);
v_head_294_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_head_294_);
lean_dec_ref_known(v_x_290_, 2);
v___x_295_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_295_, 0, v_head_294_);
return v___x_295_;
}
else
{
lean_object* v_head_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
lean_inc(v_tail_293_);
v_head_296_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_head_296_);
lean_dec_ref_known(v_x_290_, 2);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v_head_296_);
v___x_298_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7_spec__8(v_x_291_, v___x_297_, v_tail_293_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(lean_object* v___x_299_, lean_object* v_j_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_zero_302_; uint8_t v_isZero_303_; 
v_zero_302_ = lean_unsigned_to_nat(0u);
v_isZero_303_ = lean_nat_dec_eq(v_j_300_, v_zero_302_);
if (v_isZero_303_ == 1)
{
lean_dec(v_j_300_);
return v_a_301_;
}
else
{
lean_object* v_one_304_; lean_object* v_n_305_; lean_object* v___x_306_; 
v_one_304_ = lean_unsigned_to_nat(1u);
v_n_305_ = lean_nat_sub(v_j_300_, v_one_304_);
lean_dec(v_j_300_);
v___x_306_ = lean_string_utf8_next(v___x_299_, v_a_301_);
lean_dec(v_a_301_);
v_j_300_ = v_n_305_;
v_a_301_ = v___x_306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg___boxed(lean_object* v___x_308_, lean_object* v_j_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_308_, v_j_309_, v_a_310_);
lean_dec_ref(v___x_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(lean_object* v_o_315_, lean_object* v_k_316_, uint8_t v_v_317_){
_start:
{
lean_object* v_map_318_; uint8_t v_hasTrace_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_333_; 
v_map_318_ = lean_ctor_get(v_o_315_, 0);
v_hasTrace_319_ = lean_ctor_get_uint8(v_o_315_, sizeof(void*)*1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_o_315_);
if (v_isSharedCheck_333_ == 0)
{
v___x_321_ = v_o_315_;
v_isShared_322_ = v_isSharedCheck_333_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_map_318_);
lean_dec(v_o_315_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_333_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_323_, 0, v_v_317_);
lean_inc(v_k_316_);
v___x_324_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_316_, v___x_323_, v_map_318_);
if (v_hasTrace_319_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_328_; 
v___x_325_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___closed__1));
v___x_326_ = l_Lean_Name_isPrefixOf(v___x_325_, v_k_316_);
lean_dec(v_k_316_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_328_ = v___x_321_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_324_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_326_);
return v___x_328_;
}
}
else
{
lean_object* v___x_331_; 
lean_dec(v_k_316_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_324_);
v___x_331_ = v___x_321_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_324_);
lean_ctor_set_uint8(v_reuseFailAlloc_332_, sizeof(void*)*1, v_hasTrace_319_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0___boxed(lean_object* v_o_334_, lean_object* v_k_335_, lean_object* v_v_336_){
_start:
{
uint8_t v_v_boxed_337_; lean_object* v_res_338_; 
v_v_boxed_337_ = lean_unbox(v_v_336_);
v_res_338_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_o_334_, v_k_335_, v_v_boxed_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(lean_object* v_opts_339_, lean_object* v_opt_340_, uint8_t v_val_341_){
_start:
{
lean_object* v_name_342_; lean_object* v___x_343_; 
v_name_342_ = lean_ctor_get(v_opt_340_, 0);
lean_inc(v_name_342_);
lean_dec_ref(v_opt_340_);
v___x_343_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0_spec__0(v_opts_339_, v_name_342_, v_val_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0___boxed(lean_object* v_opts_344_, lean_object* v_opt_345_, lean_object* v_val_346_){
_start:
{
uint8_t v_val_boxed_347_; lean_object* v_res_348_; 
v_val_boxed_347_ = lean_unbox(v_val_346_);
v_res_348_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_opts_344_, v_opt_345_, v_val_boxed_347_);
return v_res_348_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3(void){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_353_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__3);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__4);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(size_t v_sz_359_, size_t v_i_360_, lean_object* v_bs_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_lt(v_i_360_, v_sz_359_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_368_, 0, v_bs_361_);
return v___x_368_;
}
else
{
lean_object* v_v_369_; lean_object* v_fst_370_; lean_object* v_snd_371_; lean_object* v___x_372_; lean_object* v_bs_x27_373_; lean_object* v_value_375_; 
v_v_369_ = lean_array_uget_borrowed(v_bs_361_, v_i_360_);
v_fst_370_ = lean_ctor_get(v_v_369_, 0);
lean_inc(v_fst_370_);
v_snd_371_ = lean_ctor_get(v_v_369_, 1);
lean_inc(v_snd_371_);
v___x_372_ = lean_unsigned_to_nat(0u);
v_bs_x27_373_ = lean_array_uset(v_bs_361_, v_i_360_, v___x_372_);
if (lean_obj_tag(v_snd_371_) == 1)
{
lean_object* v_val_384_; lean_object* v___x_385_; lean_object* v_toCold_386_; lean_object* v_currRecDepth_387_; lean_object* v_ref_388_; uint8_t v_suppressElabErrors_389_; lean_object* v_fileName_390_; lean_object* v_fileMap_391_; lean_object* v_options_392_; lean_object* v_currNamespace_393_; lean_object* v_openDecls_394_; lean_object* v_initHeartbeats_395_; lean_object* v_maxHeartbeats_396_; lean_object* v_quotContext_397_; lean_object* v_currMacroScope_398_; lean_object* v_cancelTk_x3f_399_; lean_object* v_inheritedTraceOptions_400_; lean_object* v_env_401_; lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v_fileName_409_; lean_object* v_fileMap_410_; lean_object* v_currNamespace_411_; lean_object* v_openDecls_412_; lean_object* v_initHeartbeats_413_; lean_object* v_maxHeartbeats_414_; lean_object* v_quotContext_415_; lean_object* v_currMacroScope_416_; lean_object* v_cancelTk_x3f_417_; lean_object* v_inheritedTraceOptions_418_; lean_object* v_currRecDepth_419_; lean_object* v_ref_420_; uint8_t v_suppressElabErrors_421_; lean_object* v___y_422_; uint8_t v___y_451_; uint8_t v___x_472_; 
v_val_384_ = lean_ctor_get(v_snd_371_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_snd_371_, 1);
v___x_385_ = lean_st_ref_get(v___y_365_);
v_toCold_386_ = lean_ctor_get(v___y_364_, 0);
v_currRecDepth_387_ = lean_ctor_get(v___y_364_, 1);
v_ref_388_ = lean_ctor_get(v___y_364_, 2);
v_suppressElabErrors_389_ = lean_ctor_get_uint8(v___y_364_, sizeof(void*)*3 + 1);
v_fileName_390_ = lean_ctor_get(v_toCold_386_, 0);
v_fileMap_391_ = lean_ctor_get(v_toCold_386_, 1);
v_options_392_ = lean_ctor_get(v_toCold_386_, 2);
v_currNamespace_393_ = lean_ctor_get(v_toCold_386_, 4);
v_openDecls_394_ = lean_ctor_get(v_toCold_386_, 5);
v_initHeartbeats_395_ = lean_ctor_get(v_toCold_386_, 6);
v_maxHeartbeats_396_ = lean_ctor_get(v_toCold_386_, 7);
v_quotContext_397_ = lean_ctor_get(v_toCold_386_, 8);
v_currMacroScope_398_ = lean_ctor_get(v_toCold_386_, 9);
v_cancelTk_x3f_399_ = lean_ctor_get(v_toCold_386_, 10);
v_inheritedTraceOptions_400_ = lean_ctor_get(v_toCold_386_, 11);
v_env_401_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_env_401_);
lean_dec(v___x_385_);
v___x_402_ = lean_box(1);
v___x_403_ = l_Lean_pp_mvars;
v___x_404_ = 0;
lean_inc_ref(v_options_392_);
v___x_405_ = l_Lean_Option_set___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__0(v_options_392_, v___x_403_, v___x_404_);
v___x_406_ = l_Lean_diagnostics;
v___x_407_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__1(v___x_405_, v___x_406_);
v___x_472_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_401_);
lean_dec_ref(v_env_401_);
if (v___x_407_ == 0)
{
if (v___x_472_ == 0)
{
v___y_451_ = v___x_367_;
goto v___jp_450_;
}
else
{
v___y_451_ = v___x_407_;
goto v___jp_450_;
}
}
else
{
v___y_451_ = v___x_472_;
goto v___jp_450_;
}
v___jp_408_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_423_ = l_Lean_maxRecDepth;
v___x_424_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___x_405_, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_425_, 0, v_fileName_409_);
lean_ctor_set(v___x_425_, 1, v_fileMap_410_);
lean_ctor_set(v___x_425_, 2, v___x_405_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
lean_ctor_set(v___x_425_, 4, v_currNamespace_411_);
lean_ctor_set(v___x_425_, 5, v_openDecls_412_);
lean_ctor_set(v___x_425_, 6, v_initHeartbeats_413_);
lean_ctor_set(v___x_425_, 7, v_maxHeartbeats_414_);
lean_ctor_set(v___x_425_, 8, v_quotContext_415_);
lean_ctor_set(v___x_425_, 9, v_currMacroScope_416_);
lean_ctor_set(v___x_425_, 10, v_cancelTk_x3f_417_);
lean_ctor_set(v___x_425_, 11, v_inheritedTraceOptions_418_);
lean_inc(v_ref_420_);
lean_inc(v_currRecDepth_419_);
v___x_426_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_currRecDepth_419_);
lean_ctor_set(v___x_426_, 2, v_ref_420_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3, v___x_407_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3 + 1, v_suppressElabErrors_421_);
v___x_427_ = l_Lean_PrettyPrinter_delab(v_val_384_, v___x_402_, v___y_362_, v___y_363_, v___x_426_, v___y_422_);
lean_dec_ref_known(v___x_426_, 3);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__2));
v___x_430_ = l_Lean_PrettyPrinter_ppCategory(v___x_429_, v_a_428_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref_known(v___x_430_, 1);
v___x_432_ = l_Std_Format_defWidth;
v___x_433_ = l_Std_Format_pretty(v_a_431_, v___x_432_, v___x_372_, v___x_372_);
v_value_375_ = v___x_433_;
goto v___jp_374_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_bs_x27_373_);
lean_dec(v_fst_370_);
v_a_434_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_430_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_430_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v_bs_x27_373_);
lean_dec(v_fst_370_);
v_a_442_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_427_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_427_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
v___jp_450_:
{
if (v___y_451_ == 0)
{
lean_object* v___x_452_; lean_object* v_env_453_; lean_object* v_nextMacroScope_454_; lean_object* v_ngen_455_; lean_object* v_auxDeclNGen_456_; lean_object* v_traceState_457_; lean_object* v_messages_458_; lean_object* v_infoState_459_; lean_object* v_snapshotTasks_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_470_; 
v___x_452_ = lean_st_ref_take(v___y_365_);
v_env_453_ = lean_ctor_get(v___x_452_, 0);
v_nextMacroScope_454_ = lean_ctor_get(v___x_452_, 1);
v_ngen_455_ = lean_ctor_get(v___x_452_, 2);
v_auxDeclNGen_456_ = lean_ctor_get(v___x_452_, 3);
v_traceState_457_ = lean_ctor_get(v___x_452_, 4);
v_messages_458_ = lean_ctor_get(v___x_452_, 6);
v_infoState_459_ = lean_ctor_get(v___x_452_, 7);
v_snapshotTasks_460_ = lean_ctor_get(v___x_452_, 8);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_470_ == 0)
{
lean_object* v_unused_471_; 
v_unused_471_ = lean_ctor_get(v___x_452_, 5);
lean_dec(v_unused_471_);
v___x_462_ = v___x_452_;
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_snapshotTasks_460_);
lean_inc(v_infoState_459_);
lean_inc(v_messages_458_);
lean_inc(v_traceState_457_);
lean_inc(v_auxDeclNGen_456_);
lean_inc(v_ngen_455_);
lean_inc(v_nextMacroScope_454_);
lean_inc(v_env_453_);
lean_dec(v___x_452_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_470_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = l_Lean_Kernel_enableDiag(v_env_453_, v___x_407_);
v___x_465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__5);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 5, v___x_465_);
lean_ctor_set(v___x_462_, 0, v___x_464_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_nextMacroScope_454_);
lean_ctor_set(v_reuseFailAlloc_469_, 2, v_ngen_455_);
lean_ctor_set(v_reuseFailAlloc_469_, 3, v_auxDeclNGen_456_);
lean_ctor_set(v_reuseFailAlloc_469_, 4, v_traceState_457_);
lean_ctor_set(v_reuseFailAlloc_469_, 5, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_469_, 6, v_messages_458_);
lean_ctor_set(v_reuseFailAlloc_469_, 7, v_infoState_459_);
lean_ctor_set(v_reuseFailAlloc_469_, 8, v_snapshotTasks_460_);
v___x_467_ = v_reuseFailAlloc_469_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; 
v___x_468_ = lean_st_ref_put(v___y_365_, v___x_467_);
lean_inc_ref(v_inheritedTraceOptions_400_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc_ref(v_fileMap_391_);
lean_inc_ref(v_fileName_390_);
v_fileName_409_ = v_fileName_390_;
v_fileMap_410_ = v_fileMap_391_;
v_currNamespace_411_ = v_currNamespace_393_;
v_openDecls_412_ = v_openDecls_394_;
v_initHeartbeats_413_ = v_initHeartbeats_395_;
v_maxHeartbeats_414_ = v_maxHeartbeats_396_;
v_quotContext_415_ = v_quotContext_397_;
v_currMacroScope_416_ = v_currMacroScope_398_;
v_cancelTk_x3f_417_ = v_cancelTk_x3f_399_;
v_inheritedTraceOptions_418_ = v_inheritedTraceOptions_400_;
v_currRecDepth_419_ = v_currRecDepth_387_;
v_ref_420_ = v_ref_388_;
v_suppressElabErrors_421_ = v_suppressElabErrors_389_;
v___y_422_ = v___y_365_;
goto v___jp_408_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_400_);
lean_inc(v_cancelTk_x3f_399_);
lean_inc(v_currMacroScope_398_);
lean_inc(v_quotContext_397_);
lean_inc(v_maxHeartbeats_396_);
lean_inc(v_initHeartbeats_395_);
lean_inc(v_openDecls_394_);
lean_inc(v_currNamespace_393_);
lean_inc_ref(v_fileMap_391_);
lean_inc_ref(v_fileName_390_);
v_fileName_409_ = v_fileName_390_;
v_fileMap_410_ = v_fileMap_391_;
v_currNamespace_411_ = v_currNamespace_393_;
v_openDecls_412_ = v_openDecls_394_;
v_initHeartbeats_413_ = v_initHeartbeats_395_;
v_maxHeartbeats_414_ = v_maxHeartbeats_396_;
v_quotContext_415_ = v_quotContext_397_;
v_currMacroScope_416_ = v_currMacroScope_398_;
v_cancelTk_x3f_417_ = v_cancelTk_x3f_399_;
v_inheritedTraceOptions_418_ = v_inheritedTraceOptions_400_;
v_currRecDepth_419_ = v_currRecDepth_387_;
v_ref_420_ = v_ref_388_;
v_suppressElabErrors_421_ = v_suppressElabErrors_389_;
v___y_422_ = v___y_365_;
goto v___jp_408_;
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec(v_snd_371_);
v___x_473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__6));
v_value_375_ = v___x_473_;
goto v___jp_374_;
}
v___jp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v___x_376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_370_, v___x_367_);
v___x_377_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___closed__0));
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
v___x_379_ = lean_string_append(v___x_378_, v_value_375_);
lean_dec_ref(v_value_375_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_360_, v___x_380_);
v___x_382_ = lean_array_uset(v_bs_x27_373_, v_i_360_, v___x_379_);
v_i_360_ = v___x_381_;
v_bs_361_ = v___x_382_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3___boxed(lean_object* v_sz_474_, lean_object* v_i_475_, lean_object* v_bs_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_474_);
lean_dec(v_sz_474_);
v_i_boxed_483_ = lean_unbox_usize(v_i_475_);
lean_dec(v_i_475_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_boxed_482_, v_i_boxed_483_, v_bs_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(lean_object* v_s_485_, lean_object* v_pos_486_){
_start:
{
lean_object* v_str_487_; lean_object* v_startInclusive_488_; lean_object* v_endExclusive_489_; lean_object* v___x_490_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v_decide_501_; 
v_str_487_ = lean_ctor_get(v_s_485_, 0);
v_startInclusive_488_ = lean_ctor_get(v_s_485_, 1);
v_endExclusive_489_ = lean_ctor_get(v_s_485_, 2);
v___x_490_ = lean_nat_add(v_startInclusive_488_, v_pos_486_);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_nat_sub(v_endExclusive_489_, v___x_490_);
v_decide_501_ = lean_nat_dec_eq(v___x_499_, v___x_500_);
lean_dec(v___x_500_);
if (v_decide_501_ == 0)
{
uint32_t v___x_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_string_utf8_get_fast(v_str_487_, v___x_490_);
v___x_503_ = 32;
v___x_504_ = lean_uint32_dec_eq(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 9;
v___x_506_ = lean_uint32_dec_eq(v___x_502_, v___x_505_);
if (v___x_506_ == 0)
{
uint32_t v___x_507_; uint8_t v___x_508_; 
v___x_507_ = 13;
v___x_508_ = lean_uint32_dec_eq(v___x_502_, v___x_507_);
if (v___x_508_ == 0)
{
uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_509_ = 10;
v___x_510_ = lean_uint32_dec_eq(v___x_502_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v___x_490_);
return v_pos_486_;
}
else
{
goto v___jp_491_;
}
}
else
{
goto v___jp_491_;
}
}
else
{
goto v___jp_491_;
}
}
else
{
goto v___jp_491_;
}
}
else
{
lean_dec(v___x_490_);
return v_pos_486_;
}
v___jp_491_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_492_ = lean_string_utf8_next_fast(v_str_487_, v___x_490_);
v___x_493_ = lean_nat_sub(v___x_492_, v___x_490_);
lean_dec(v___x_490_);
v___x_494_ = lean_nat_add(v_pos_486_, v___x_493_);
lean_dec(v___x_493_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_pos_486_, v___x_495_);
v___x_497_ = lean_nat_dec_le(v___x_496_, v___x_494_);
lean_dec(v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v___x_494_);
return v_pos_486_;
}
else
{
lean_dec(v_pos_486_);
v_pos_486_ = v___x_494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5___boxed(lean_object* v_s_511_, lean_object* v_pos_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v_s_511_, v_pos_512_);
lean_dec_ref(v_s_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(lean_object* v_as_516_, size_t v_i_517_, size_t v_stop_518_, lean_object* v_b_519_){
_start:
{
uint8_t v___x_520_; 
v___x_520_ = lean_usize_dec_eq(v_i_517_, v_stop_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; size_t v___x_528_; size_t v___x_529_; 
v___x_521_ = lean_array_uget_borrowed(v_as_516_, v_i_517_);
v___x_522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___closed__0));
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v_b_519_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_box(1);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
lean_inc(v___x_521_);
v___x_526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_521_);
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_517_, v___x_528_);
v_i_517_ = v___x_529_;
v_b_519_ = v___x_527_;
goto _start;
}
else
{
return v_b_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8___boxed(lean_object* v_as_531_, lean_object* v_i_532_, lean_object* v_stop_533_, lean_object* v_b_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_532_);
lean_dec(v_i_532_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_533_);
lean_dec(v_stop_533_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_as_531_, v_i_boxed_535_, v_stop_boxed_536_, v_b_534_);
lean_dec_ref(v_as_531_);
return v_res_537_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__2));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_550_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__8));
v___x_551_ = lean_unsigned_to_nat(14u);
v___x_552_ = lean_unsigned_to_nat(22u);
v___x_553_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__7));
v___x_554_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__6));
v___x_555_ = l_mkPanicMessageWithDecl(v___x_554_, v___x_553_, v___x_552_, v___x_551_, v___x_550_);
return v___x_555_;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1(void){
_start:
{
uint32_t v___x_556_; lean_object* v___x_557_; 
v___x_556_ = 32;
v___x_557_ = lean_box_uint32(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(lean_object* v_fields_558_, lean_object* v_stx_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; 
lean_inc(v_stx_559_);
v___x_565_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_mkFieldsHintView_x3f(v_stx_559_);
if (lean_obj_tag(v___x_565_) == 1)
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_810_; 
v_val_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_810_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_810_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_810_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
size_t v_sz_570_; size_t v___x_571_; lean_object* v___x_572_; 
v_sz_570_ = lean_array_size(v_fields_558_);
v___x_571_ = ((size_t)0ULL);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__3(v_sz_570_, v___x_571_, v_fields_558_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_801_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_isSingleLineStyle___redArg(v_stx_559_, v_val_566_, v_a_562_);
lean_dec(v_stx_559_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_801_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_801_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_801_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___x_579_; lean_object* v___y_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v_fst_617_; lean_object* v_snd_618_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_652_; lean_object* v___y_653_; uint8_t v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; uint8_t v___y_660_; lean_object* v___y_661_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; uint8_t v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; uint8_t v___y_676_; lean_object* v___y_677_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; uint8_t v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; uint8_t v___y_690_; lean_object* v___y_691_; lean_object* v_startInclusive_692_; lean_object* v_endExclusive_693_; lean_object* v___y_701_; lean_object* v___y_702_; uint8_t v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; uint8_t v___y_710_; lean_object* v___y_711_; lean_object* v___y_717_; uint8_t v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; uint8_t v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; uint8_t v___y_729_; uint8_t v___y_730_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_771_; lean_object* v___y_785_; uint8_t v___x_788_; 
v___x_579_ = 1;
v___x_788_ = lean_unbox(v_a_575_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_array_to_list(v_a_573_);
v___x_790_ = lean_box(1);
v___x_791_ = l_Std_Format_joinSep___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__7(v___x_789_, v___x_790_);
v___y_771_ = v___x_791_;
goto v___jp_770_;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_792_ = lean_box(0);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_array_get_size(v_a_573_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v_a_573_);
v___y_785_ = v___x_792_;
goto v___jp_784_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = lean_nat_dec_le(v___x_794_, v___x_794_);
if (v___x_796_ == 0)
{
if (v___x_795_ == 0)
{
lean_dec(v_a_573_);
v___y_785_ = v___x_792_;
goto v___jp_784_;
}
else
{
size_t v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_usize_of_nat(v___x_794_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_573_, v___x_571_, v___x_797_, v___x_792_);
lean_dec(v_a_573_);
v___y_785_ = v___x_798_;
goto v___jp_784_;
}
}
else
{
size_t v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_usize_of_nat(v___x_794_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__8(v_a_573_, v___x_571_, v___x_799_, v___x_792_);
lean_dec(v_a_573_);
v___y_785_ = v___x_800_;
goto v___jp_784_;
}
}
}
v___jp_580_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_586_ = l_Lean_Meta_Tactic_TryThis_format_inputWidth;
v___x_587_ = l_Lean_Option_get___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__2(v___y_581_, v___x_586_);
lean_dec_ref(v___y_581_);
lean_inc(v___y_585_);
v___x_588_ = lean_apply_1(v___y_582_, v___y_585_);
v___x_589_ = l_Std_Format_pretty(v___y_584_, v___x_587_, v___y_583_, v___x_588_);
lean_dec(v___x_587_);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 1);
lean_ctor_set(v___x_577_, 0, v___x_589_);
v___x_591_ = v___x_577_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_608_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__1));
v___x_594_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_594_, 0, v___x_591_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_592_);
lean_ctor_set(v___x_594_, 3, v___x_592_);
lean_ctor_set(v___x_594_, 4, v___x_592_);
lean_ctor_set(v___x_594_, 5, v___x_593_);
lean_inc(v___y_585_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___y_585_);
lean_ctor_set(v___x_595_, 1, v___y_585_);
v___x_596_ = l_Lean_Syntax_ofRange(v___x_595_, v___x_579_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_596_);
v___x_598_ = v___x_568_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_607_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_599_ = 0;
v___x_600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_600_, 0, v___x_594_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_592_);
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*3, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__3);
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
v___x_604_ = lean_array_push(v___x_603_, v___x_600_);
v___x_605_ = 0;
v___x_606_ = l_Lean_MessageData_hint(v___x_601_, v___x_604_, v___x_592_, v___x_592_, v___x_605_, v_a_562_, v_a_563_);
lean_dec_ref(v___x_604_);
return v___x_606_;
}
}
}
v___jp_609_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v_fst_617_);
lean_ctor_set(v___x_619_, 1, v___y_610_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_snd_618_);
if (lean_obj_tag(v___y_615_) == 0)
{
if (lean_obj_tag(v___y_616_) == 0)
{
v___y_581_ = v___y_611_;
v___y_582_ = v___y_613_;
v___y_583_ = v___y_614_;
v___y_584_ = v___x_620_;
v___y_585_ = v___y_612_;
goto v___jp_580_;
}
else
{
lean_object* v_val_621_; 
lean_dec(v___y_612_);
v_val_621_ = lean_ctor_get(v___y_616_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v___y_616_, 1);
v___y_581_ = v___y_611_;
v___y_582_ = v___y_613_;
v___y_583_ = v___y_614_;
v___y_584_ = v___x_620_;
v___y_585_ = v_val_621_;
goto v___jp_580_;
}
}
else
{
lean_object* v_val_622_; 
lean_dec(v___y_616_);
lean_dec(v___y_612_);
v_val_622_ = lean_ctor_get(v___y_615_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___y_615_, 1);
v___y_581_ = v___y_611_;
v___y_582_ = v___y_613_;
v___y_583_ = v___y_614_;
v___y_584_ = v___x_620_;
v___y_585_ = v_val_622_;
goto v___jp_580_;
}
}
v___jp_623_:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(1);
v___x_632_ = lean_box(0);
v___y_610_ = v___y_624_;
v___y_611_ = v___y_625_;
v___y_612_ = v___y_626_;
v___y_613_ = v___y_627_;
v___y_614_ = v___y_628_;
v___y_615_ = v___y_629_;
v___y_616_ = v___y_630_;
v_fst_617_ = v___x_631_;
v_snd_618_ = v___x_632_;
goto v___jp_609_;
}
v___jp_633_:
{
if (lean_obj_tag(v___y_640_) == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box(1);
v___x_642_ = lean_box(0);
v___y_610_ = v___y_634_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_636_;
v___y_613_ = v___y_637_;
v___y_614_ = v___y_638_;
v___y_615_ = v___y_639_;
v___y_616_ = v___y_640_;
v_fst_617_ = v___x_641_;
v_snd_618_ = v___x_642_;
goto v___jp_609_;
}
else
{
lean_object* v_val_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_val_643_ = lean_ctor_get(v___y_640_, 0);
lean_inc_ref(v___y_637_);
lean_inc(v_val_643_);
v___x_644_ = lean_apply_1(v___y_637_, v_val_643_);
v___x_645_ = lean_nat_sub(v___y_638_, v___x_644_);
lean_dec(v___x_644_);
v___x_646_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed__const__1;
v___x_647_ = l_List_replicateTR___redArg(v___x_645_, v___x_646_);
v___x_648_ = lean_string_mk(v___x_647_);
v___x_649_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
v___x_650_ = lean_box(0);
v___y_610_ = v___y_634_;
v___y_611_ = v___y_635_;
v___y_612_ = v___y_636_;
v___y_613_ = v___y_637_;
v___y_614_ = v___y_638_;
v___y_615_ = v___y_639_;
v___y_616_ = v___y_640_;
v_fst_617_ = v___x_649_;
v_snd_618_ = v___x_650_;
goto v___jp_609_;
}
}
v___jp_651_:
{
uint8_t v___x_662_; 
v___x_662_ = lean_unbox(v_a_575_);
lean_dec(v_a_575_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_nat_dec_lt(v___x_663_, v___y_657_);
lean_dec(v___y_657_);
if (v___x_664_ == 0)
{
if (v___y_654_ == 0)
{
if (v___y_660_ == 0)
{
lean_object* v___x_665_; 
v___x_665_ = ((lean_object*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__5));
v___y_610_ = v___y_652_;
v___y_611_ = v___y_653_;
v___y_612_ = v___y_655_;
v___y_613_ = v___y_656_;
v___y_614_ = v___y_658_;
v___y_615_ = v___y_659_;
v___y_616_ = v___y_661_;
v_fst_617_ = v___x_665_;
v_snd_618_ = v___x_665_;
goto v___jp_609_;
}
else
{
v___y_634_ = v___y_652_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_655_;
v___y_637_ = v___y_656_;
v___y_638_ = v___y_658_;
v___y_639_ = v___y_659_;
v___y_640_ = v___y_661_;
goto v___jp_633_;
}
}
else
{
if (v___y_660_ == 0)
{
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
v___y_626_ = v___y_655_;
v___y_627_ = v___y_656_;
v___y_628_ = v___y_658_;
v___y_629_ = v___y_659_;
v___y_630_ = v___y_661_;
goto v___jp_623_;
}
else
{
v___y_634_ = v___y_652_;
v___y_635_ = v___y_653_;
v___y_636_ = v___y_655_;
v___y_637_ = v___y_656_;
v___y_638_ = v___y_658_;
v___y_639_ = v___y_659_;
v___y_640_ = v___y_661_;
goto v___jp_633_;
}
}
}
else
{
v___y_624_ = v___y_652_;
v___y_625_ = v___y_653_;
v___y_626_ = v___y_655_;
v___y_627_ = v___y_656_;
v___y_628_ = v___y_658_;
v___y_629_ = v___y_659_;
v___y_630_ = v___y_661_;
goto v___jp_623_;
}
}
else
{
lean_object* v___x_666_; 
lean_dec(v___y_657_);
v___x_666_ = lean_box(0);
v___y_610_ = v___y_652_;
v___y_611_ = v___y_653_;
v___y_612_ = v___y_655_;
v___y_613_ = v___y_656_;
v___y_614_ = v___y_658_;
v___y_615_ = v___y_659_;
v___y_616_ = v___y_661_;
v_fst_617_ = v___x_666_;
v_snd_618_ = v___x_666_;
goto v___jp_609_;
}
}
v___jp_667_:
{
lean_object* v___x_678_; 
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___y_677_);
v___y_652_ = v___y_668_;
v___y_653_ = v___y_669_;
v___y_654_ = v___y_671_;
v___y_655_ = v___y_670_;
v___y_656_ = v___y_672_;
v___y_657_ = v___y_674_;
v___y_658_ = v___y_673_;
v___y_659_ = v___y_675_;
v___y_660_ = v___y_676_;
v___y_661_ = v___x_678_;
goto v___jp_651_;
}
v___jp_679_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v_decide_697_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_String_Slice_Pos_skipWhile___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__5(v___y_691_, v___x_694_);
lean_dec_ref(v___y_691_);
v___x_696_ = lean_nat_sub(v_endExclusive_693_, v_startInclusive_692_);
lean_dec(v_startInclusive_692_);
lean_dec(v_endExclusive_693_);
v_decide_697_ = lean_nat_dec_eq(v___x_695_, v___x_696_);
lean_dec(v___x_696_);
lean_dec(v___x_695_);
if (v_decide_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec(v___y_689_);
lean_dec(v___y_687_);
v___x_698_ = lean_box(0);
v___y_652_ = v___y_680_;
v___y_653_ = v___y_681_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_682_;
v___y_656_ = v___y_684_;
v___y_657_ = v___y_686_;
v___y_658_ = v___y_685_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_690_;
v___y_661_ = v___x_698_;
goto v___jp_651_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_le(v___y_687_, v___y_689_);
if (v___x_699_ == 0)
{
lean_dec(v___y_687_);
v___y_668_ = v___y_680_;
v___y_669_ = v___y_681_;
v___y_670_ = v___y_682_;
v___y_671_ = v___y_683_;
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_688_;
v___y_676_ = v___y_690_;
v___y_677_ = v___y_689_;
goto v___jp_667_;
}
else
{
lean_dec(v___y_689_);
v___y_668_ = v___y_680_;
v___y_669_ = v___y_681_;
v___y_670_ = v___y_682_;
v___y_671_ = v___y_683_;
v___y_672_ = v___y_684_;
v___y_673_ = v___y_685_;
v___y_674_ = v___y_686_;
v___y_675_ = v___y_688_;
v___y_676_ = v___y_690_;
v___y_677_ = v___y_687_;
goto v___jp_667_;
}
}
}
v___jp_700_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_startInclusive_714_; lean_object* v_endExclusive_715_; 
v___x_712_ = lean_obj_once(&l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9, &l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9_once, _init_l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___closed__9);
v___x_713_ = l_panic___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__6(v___x_712_);
v_startInclusive_714_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_startInclusive_714_);
v_endExclusive_715_ = lean_ctor_get(v___x_713_, 2);
lean_inc(v_endExclusive_715_);
v___y_680_ = v___y_701_;
v___y_681_ = v___y_702_;
v___y_682_ = v___y_704_;
v___y_683_ = v___y_703_;
v___y_684_ = v___y_705_;
v___y_685_ = v___y_707_;
v___y_686_ = v___y_706_;
v___y_687_ = v___y_708_;
v___y_688_ = v___y_709_;
v___y_689_ = v___y_711_;
v___y_690_ = v___y_710_;
v___y_691_ = v___x_713_;
v_startInclusive_692_ = v_startInclusive_714_;
v_endExclusive_693_ = v_endExclusive_715_;
goto v___jp_679_;
}
v___jp_716_:
{
if (v___y_721_ == 0)
{
lean_dec_ref(v___y_717_);
v___y_701_ = v___y_723_;
v___y_702_ = v___y_724_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_725_;
v___y_707_ = v___y_726_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_728_;
v___y_710_ = v___y_729_;
v___y_711_ = v___y_722_;
goto v___jp_700_;
}
else
{
if (v___y_730_ == 0)
{
lean_dec_ref(v___y_717_);
v___y_701_ = v___y_723_;
v___y_702_ = v___y_724_;
v___y_703_ = v___y_718_;
v___y_704_ = v___y_719_;
v___y_705_ = v___y_720_;
v___y_706_ = v___y_725_;
v___y_707_ = v___y_726_;
v___y_708_ = v___y_727_;
v___y_709_ = v___y_728_;
v___y_710_ = v___y_729_;
v___y_711_ = v___y_722_;
goto v___jp_700_;
}
else
{
lean_object* v___x_731_; 
lean_inc_n(v___y_722_, 2);
lean_inc_n(v___y_719_, 2);
v___x_731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_731_, 0, v___y_717_);
lean_ctor_set(v___x_731_, 1, v___y_719_);
lean_ctor_set(v___x_731_, 2, v___y_722_);
v___y_680_ = v___y_723_;
v___y_681_ = v___y_724_;
v___y_682_ = v___y_719_;
v___y_683_ = v___y_718_;
v___y_684_ = v___y_720_;
v___y_685_ = v___y_726_;
v___y_686_ = v___y_725_;
v___y_687_ = v___y_727_;
v___y_688_ = v___y_728_;
v___y_689_ = v___y_722_;
v___y_690_ = v___y_729_;
v___y_691_ = v___x_731_;
v_startInclusive_692_ = v___y_719_;
v_endExclusive_693_ = v___y_722_;
goto v___jp_679_;
}
}
}
v___jp_732_:
{
lean_object* v_lastFieldTailPos_x3f_738_; uint8_t v_hasWith_739_; lean_object* v_numFields_740_; lean_object* v_leaderPos_741_; lean_object* v_leaderTailPos_742_; lean_object* v_closingPos_743_; lean_object* v___x_744_; lean_object* v_line_745_; lean_object* v___x_746_; lean_object* v_line_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_lastFieldTailPos_x3f_738_ = lean_ctor_get(v_val_566_, 1);
lean_inc(v_lastFieldTailPos_x3f_738_);
v_hasWith_739_ = lean_ctor_get_uint8(v_val_566_, sizeof(void*)*7);
v_numFields_740_ = lean_ctor_get(v_val_566_, 2);
lean_inc(v_numFields_740_);
v_leaderPos_741_ = lean_ctor_get(v_val_566_, 4);
lean_inc(v_leaderPos_741_);
v_leaderTailPos_742_ = lean_ctor_get(v_val_566_, 5);
lean_inc(v_leaderTailPos_742_);
v_closingPos_743_ = lean_ctor_get(v_val_566_, 6);
lean_inc(v_closingPos_743_);
lean_dec(v_val_566_);
lean_inc_ref_n(v___y_736_, 2);
v___x_744_ = l_Lean_FileMap_utf8PosToLspPos(v___y_736_, v_leaderPos_741_);
lean_dec(v_leaderPos_741_);
v_line_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_line_745_);
lean_dec_ref(v___x_744_);
v___x_746_ = l_Lean_FileMap_utf8PosToLspPos(v___y_736_, v_closingPos_743_);
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
v_source_752_ = lean_ctor_get(v___y_736_, 0);
lean_inc_ref_n(v_source_752_, 3);
lean_dec_ref(v___y_736_);
v___x_753_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_752_, v_leaderTailPos_742_);
v___x_754_ = lean_nat_add(v___y_737_, v___x_749_);
lean_inc(v___x_753_);
v___x_755_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v_source_752_, v___x_754_, v___x_753_);
v___x_756_ = lean_string_utf8_next(v_source_752_, v___x_753_);
lean_dec(v___x_753_);
v___x_757_ = l___private_Lean_Elab_StructInstHint_0__Lean_Elab_Term_StructInst_mkMissingFieldsHint_findLineEnd(v_source_752_, v___x_756_);
lean_dec(v___x_756_);
v___x_758_ = lean_string_is_valid_pos(v_source_752_, v_leaderTailPos_742_);
v___x_759_ = lean_string_is_valid_pos(v_source_752_, v___x_757_);
if (v___x_759_ == 0)
{
v___y_717_ = v_source_752_;
v___y_718_ = v_hasWith_739_;
v___y_719_ = v_leaderTailPos_742_;
v___y_720_ = v___y_735_;
v___y_721_ = v___x_758_;
v___y_722_ = v___x_757_;
v___y_723_ = v___y_733_;
v___y_724_ = v___y_734_;
v___y_725_ = v_numFields_740_;
v___y_726_ = v___y_737_;
v___y_727_ = v___x_755_;
v___y_728_ = v_lastFieldTailPos_x3f_738_;
v___y_729_ = v___x_748_;
v___y_730_ = v___x_759_;
goto v___jp_716_;
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_nat_dec_le(v_leaderTailPos_742_, v___x_757_);
v___y_717_ = v_source_752_;
v___y_718_ = v_hasWith_739_;
v___y_719_ = v_leaderTailPos_742_;
v___y_720_ = v___y_735_;
v___y_721_ = v___x_758_;
v___y_722_ = v___x_757_;
v___y_723_ = v___y_733_;
v___y_724_ = v___y_734_;
v___y_725_ = v_numFields_740_;
v___y_726_ = v___y_737_;
v___y_727_ = v___x_755_;
v___y_728_ = v_lastFieldTailPos_x3f_738_;
v___y_729_ = v___x_748_;
v___y_730_ = v___x_760_;
goto v___jp_716_;
}
}
else
{
lean_object* v___x_761_; 
lean_dec_ref(v___y_736_);
v___x_761_ = lean_box(0);
v___y_652_ = v___y_733_;
v___y_653_ = v___y_734_;
v___y_654_ = v_hasWith_739_;
v___y_655_ = v_leaderTailPos_742_;
v___y_656_ = v___y_735_;
v___y_657_ = v_numFields_740_;
v___y_658_ = v___y_737_;
v___y_659_ = v_lastFieldTailPos_x3f_738_;
v___y_660_ = v___x_748_;
v___y_661_ = v___x_761_;
goto v___jp_651_;
}
}
v___jp_762_:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(2u);
v___x_769_ = lean_nat_add(v___y_767_, v___x_768_);
lean_dec(v___y_767_);
v___y_733_ = v___y_763_;
v___y_734_ = v___y_764_;
v___y_735_ = v___y_766_;
v___y_736_ = v___y_765_;
v___y_737_ = v___x_769_;
goto v___jp_732_;
}
v___jp_770_:
{
lean_object* v_toCold_772_; lean_object* v_fileMap_773_; lean_object* v_options_774_; lean_object* v_initFieldPos_x3f_775_; lean_object* v_openingPos_776_; lean_object* v_closingPos_777_; lean_object* v___f_778_; 
v_toCold_772_ = lean_ctor_get(v_a_562_, 0);
v_fileMap_773_ = lean_ctor_get(v_toCold_772_, 1);
v_options_774_ = lean_ctor_get(v_toCold_772_, 2);
v_initFieldPos_x3f_775_ = lean_ctor_get(v_val_566_, 0);
v_openingPos_776_ = lean_ctor_get(v_val_566_, 3);
v_closingPos_777_ = lean_ctor_get(v_val_566_, 6);
lean_inc_ref(v_fileMap_773_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1___boxed), 2, 1);
lean_closure_set(v___f_778_, 0, v_fileMap_773_);
if (lean_obj_tag(v_initFieldPos_x3f_775_) == 1)
{
lean_object* v_val_779_; lean_object* v___x_780_; 
v_val_779_ = lean_ctor_get(v_initFieldPos_x3f_775_, 0);
lean_inc_ref_n(v_fileMap_773_, 2);
v___x_780_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_773_, v_val_779_);
lean_inc_ref(v_options_774_);
v___y_733_ = v___y_771_;
v___y_734_ = v_options_774_;
v___y_735_ = v___f_778_;
v___y_736_ = v_fileMap_773_;
v___y_737_ = v___x_780_;
goto v___jp_732_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
lean_inc_ref_n(v_fileMap_773_, 2);
v___x_781_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_773_, v_openingPos_776_);
v___x_782_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___lam__1(v_fileMap_773_, v_closingPos_777_);
v___x_783_ = lean_nat_dec_le(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_dec(v___x_781_);
lean_inc_ref(v_fileMap_773_);
lean_inc_ref(v_options_774_);
v___y_763_ = v___y_771_;
v___y_764_ = v_options_774_;
v___y_765_ = v_fileMap_773_;
v___y_766_ = v___f_778_;
v___y_767_ = v___x_782_;
goto v___jp_762_;
}
else
{
lean_dec(v___x_782_);
lean_inc_ref(v_fileMap_773_);
lean_inc_ref(v_options_774_);
v___y_763_ = v___y_771_;
v___y_764_ = v_options_774_;
v___y_765_ = v_fileMap_773_;
v___y_766_ = v___f_778_;
v___y_767_ = v___x_781_;
goto v___jp_762_;
}
}
}
v___jp_784_:
{
uint8_t v___x_786_; lean_object* v___x_787_; 
v___x_786_ = 1;
v___x_787_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_787_, 0, v___y_785_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*1, v___x_786_);
v___y_771_ = v___x_787_;
goto v___jp_770_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_568_);
lean_dec(v_val_566_);
lean_dec(v_stx_559_);
v_a_802_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_572_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_572_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v___x_565_);
lean_dec(v_stx_559_);
lean_dec_ref(v_fields_558_);
v___x_811_ = l_Lean_MessageData_nil;
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkMissingFieldsHint___boxed(lean_object* v_fields_813_, lean_object* v_stx_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Elab_Term_StructInst_mkMissingFieldsHint(v_fields_813_, v_stx_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(lean_object* v___x_821_, lean_object* v_n_822_, lean_object* v_j_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___redArg(v___x_821_, v_j_823_, v_a_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4___boxed(lean_object* v___x_827_, lean_object* v_n_828_, lean_object* v_j_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_Elab_Term_StructInst_mkMissingFieldsHint_spec__4(v___x_827_, v_n_828_, v_j_829_, v_a_830_, v_a_831_);
lean_dec(v_n_828_);
lean_dec_ref(v___x_827_);
return v_res_832_;
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
