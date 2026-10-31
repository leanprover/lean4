// Lean compiler output
// Module: Init.Data.Vector.Basic
// Imports: import Init.Data.Array.Nat public import Init.Data.Array.DecidableEq import Init.Data.Array.InsertIdx import Init.Data.Array.MapIdx import Init.Omega
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_mark_linear(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_append___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_repr(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__0 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term#v[_,]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__1 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value_aux_0),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 133, 146, 175, 235, 143, 200, 186)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__2 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__3 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__4 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#v["};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__5 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__6 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__7 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__7_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__8 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__9 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__10 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__11 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__12 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__13 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__14 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__15 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__16 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__17 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__18 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__19 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__20 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__21 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value;
LEAN_EXPORT const lean_object* l_Vector_term_x23v_x5b___x2c_x5d = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__21_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value_aux_2),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Vector.mk"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(253, 158, 113, 206, 216, 2, 54, 152)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__9_value),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__11_value)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value_aux_2),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24_value;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26;
static const lean_string_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value;
static lean_once_cell_t l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value;
static const lean_ctor_object l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31 = (const lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31_value;
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__0 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__0_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_Vector_repr___redArg___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__1 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__1_value;
static lean_once_cell_t l_Vector_Vector_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_Vector_repr___redArg___closed__2;
static lean_once_cell_t l_Vector_Vector_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_Vector_repr___redArg___closed__3;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__5_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__4 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__4_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__5 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__5_value;
static const lean_string_object l_Vector_Vector_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "#v[]"};
static const lean_object* l_Vector_Vector_repr___redArg___closed__6 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__6_value;
static const lean_ctor_object l_Vector_Vector_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_Vector_repr___redArg___closed__6_value)}};
static const lean_object* l_Vector_Vector_repr___redArg___closed__7 = (const lean_object*)&l_Vector_Vector_repr___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_instGetElemNatLt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_instGetElemNatLt___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_instGetElemNatLt___redArg___closed__0 = (const lean_object*)&l_Vector_instGetElemNatLt___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg();
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg();
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_head(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_set___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Vector_set___auto__1___closed__0 = (const lean_object*)&l_Vector_set___auto__1___closed__0_value;
static const lean_string_object l_Vector_set___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Vector_set___auto__1___closed__1 = (const lean_object*)&l_Vector_set___auto__1___closed__1_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__2_value_aux_2),((lean_object*)&l_Vector_set___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Vector_set___auto__1___closed__2 = (const lean_object*)&l_Vector_set___auto__1___closed__2_value;
static const lean_array_object l_Vector_set___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_set___auto__1___closed__3 = (const lean_object*)&l_Vector_set___auto__1___closed__3_value;
static const lean_string_object l_Vector_set___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Vector_set___auto__1___closed__4 = (const lean_object*)&l_Vector_set___auto__1___closed__4_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_set___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_set___auto__1___closed__5_value_aux_2),((lean_object*)&l_Vector_set___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Vector_set___auto__1___closed__5 = (const lean_object*)&l_Vector_set___auto__1___closed__5_value;
static const lean_string_object l_Vector_set___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticGet_elem_tactic"};
static const lean_object* l_Vector_set___auto__1___closed__6 = (const lean_object*)&l_Vector_set___auto__1___closed__6_value;
static const lean_ctor_object l_Vector_set___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_set___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 31, 109, 153, 11, 229, 201, 51)}};
static const lean_object* l_Vector_set___auto__1___closed__7 = (const lean_object*)&l_Vector_set___auto__1___closed__7_value;
static const lean_string_object l_Vector_set___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "get_elem_tactic"};
static const lean_object* l_Vector_set___auto__1___closed__8 = (const lean_object*)&l_Vector_set___auto__1___closed__8_value;
static lean_once_cell_t l_Vector_set___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__9;
static lean_once_cell_t l_Vector_set___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__10;
static lean_once_cell_t l_Vector_set___auto__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__11;
static lean_once_cell_t l_Vector_set___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__12;
static lean_once_cell_t l_Vector_set___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__13;
static lean_once_cell_t l_Vector_set___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__14;
static lean_once_cell_t l_Vector_set___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__15;
static lean_once_cell_t l_Vector_set___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__16;
static lean_once_cell_t l_Vector_set___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_set___auto__1___closed__17;
LEAN_EXPORT lean_object* l_Vector_set___auto__1;
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__0 = (const lean_object*)&l_Vector_foldl___redArg___closed__0_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__1 = (const lean_object*)&l_Vector_foldl___redArg___closed__1_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__2 = (const lean_object*)&l_Vector_foldl___redArg___closed__2_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__3 = (const lean_object*)&l_Vector_foldl___redArg___closed__3_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__4 = (const lean_object*)&l_Vector_foldl___redArg___closed__4_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__5 = (const lean_object*)&l_Vector_foldl___redArg___closed__5_value;
static const lean_closure_object l_Vector_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_foldl___redArg___closed__6 = (const lean_object*)&l_Vector_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__0_value),((lean_object*)&l_Vector_foldl___redArg___closed__1_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__7 = (const lean_object*)&l_Vector_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__7_value),((lean_object*)&l_Vector_foldl___redArg___closed__2_value),((lean_object*)&l_Vector_foldl___redArg___closed__3_value),((lean_object*)&l_Vector_foldl___redArg___closed__4_value),((lean_object*)&l_Vector_foldl___redArg___closed__5_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__8 = (const lean_object*)&l_Vector_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Vector_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_foldl___redArg___closed__8_value),((lean_object*)&l_Vector_foldl___redArg___closed__6_value)}};
static const lean_object* l_Vector_foldl___redArg___closed__9 = (const lean_object*)&l_Vector_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Vector_mapM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_mapM___redArg___closed__0 = (const lean_object*)&l_Vector_mapM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Vector_flatten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_flatten___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_flatten___redArg___closed__0 = (const lean_object*)&l_Vector_flatten___redArg___closed__0_value;
static const lean_array_object l_Vector_flatten___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Vector_flatten___redArg___closed__1 = (const lean_object*)&l_Vector_flatten___redArg___closed__1_value;
static const lean_closure_object l_Vector_flatten___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_append___redArg___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_flatten___redArg___closed__2 = (const lean_object*)&l_Vector_flatten___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___auto__1;
LEAN_EXPORT lean_object* l_Vector_swap___auto__3;
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___auto__1;
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Init.Data.Array.Basic"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__0 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__0_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Array.swapAt!"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__1 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__1_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "index "};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__2 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__2_value;
static const lean_string_object l_Vector_swapAt_x21___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = " out of bounds"};
static const lean_object* l_Vector_swapAt_x21___redArg___closed__3 = (const lean_object*)&l_Vector_swapAt_x21___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_range(lean_object*);
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx___auto__1;
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.Vector.Basic"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__0 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__0_value;
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Vector.eraseIdx!"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__1 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__1_value;
static const lean_string_object l_Vector_eraseIdx_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "index out of bounds"};
static const lean_object* l_Vector_eraseIdx_x21___redArg___closed__2 = (const lean_object*)&l_Vector_eraseIdx_x21___redArg___closed__2_value;
static lean_once_cell_t l_Vector_eraseIdx_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_eraseIdx_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___auto__1;
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_insertIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Vector.insertIdx!"};
static const lean_object* l_Vector_insertIdx_x21___redArg___closed__0 = (const lean_object*)&l_Vector_insertIdx_x21___redArg___closed__0_value;
static lean_once_cell_t l_Vector_insertIdx_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_insertIdx_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_findM_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_findM_x3f___redArg___closed__0 = (const lean_object*)&l_Vector_findM_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___redArg();
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE___redArg();
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Vector_lex___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Vector_lex___auto__1___closed__0 = (const lean_object*)&l_Vector_lex___auto__1___closed__0_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_1),((lean_object*)&l_Vector_set___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__1_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Vector_lex___auto__1___closed__1 = (const lean_object*)&l_Vector_lex___auto__1___closed__1_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__2;
static lean_once_cell_t l_Vector_lex___auto__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__3;
static const lean_string_object l_Vector_lex___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Vector_lex___auto__1___closed__4 = (const lean_object*)&l_Vector_lex___auto__1___closed__4_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__5_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Vector_lex___auto__1___closed__5 = (const lean_object*)&l_Vector_lex___auto__1___closed__5_value;
static const lean_string_object l_Vector_lex___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Vector_lex___auto__1___closed__6 = (const lean_object*)&l_Vector_lex___auto__1___closed__6_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__7_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Vector_lex___auto__1___closed__7 = (const lean_object*)&l_Vector_lex___auto__1___closed__7_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__8;
static lean_once_cell_t l_Vector_lex___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__9;
static const lean_string_object l_Vector_lex___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Vector_lex___auto__1___closed__10 = (const lean_object*)&l_Vector_lex___auto__1___closed__10_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Vector_lex___auto__1___closed__11 = (const lean_object*)&l_Vector_lex___auto__1___closed__11_value;
static const lean_string_object l_Vector_lex___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Vector_lex___auto__1___closed__12 = (const lean_object*)&l_Vector_lex___auto__1___closed__12_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Vector_lex___auto__1___closed__13 = (const lean_object*)&l_Vector_lex___auto__1___closed__13_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_lex___auto__1___closed__14 = (const lean_object*)&l_Vector_lex___auto__1___closed__14_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__15;
static lean_once_cell_t l_Vector_lex___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__16;
static lean_once_cell_t l_Vector_lex___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__17;
static lean_once_cell_t l_Vector_lex___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__18;
static lean_once_cell_t l_Vector_lex___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__19;
static const lean_string_object l_Vector_lex___auto__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Vector_lex___auto__1___closed__20 = (const lean_object*)&l_Vector_lex___auto__1___closed__20_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Vector_lex___auto__1___closed__21 = (const lean_object*)&l_Vector_lex___auto__1___closed__21_value;
static const lean_string_object l_Vector_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Vector_lex___auto__1___closed__22 = (const lean_object*)&l_Vector_lex___auto__1___closed__22_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__23_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Vector_lex___auto__1___closed__23 = (const lean_object*)&l_Vector_lex___auto__1___closed__23_value;
static const lean_string_object l_Vector_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Vector_lex___auto__1___closed__24 = (const lean_object*)&l_Vector_lex___auto__1___closed__24_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__25;
static lean_once_cell_t l_Vector_lex___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__26;
static lean_once_cell_t l_Vector_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__27;
static lean_once_cell_t l_Vector_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__28;
static lean_once_cell_t l_Vector_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__29;
static const lean_string_object l_Vector_lex___auto__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Vector_lex___auto__1___closed__30 = (const lean_object*)&l_Vector_lex___auto__1___closed__30_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__31;
static lean_once_cell_t l_Vector_lex___auto__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__32;
static lean_once_cell_t l_Vector_lex___auto__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__33;
static lean_once_cell_t l_Vector_lex___auto__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__34;
static lean_once_cell_t l_Vector_lex___auto__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__35;
static lean_once_cell_t l_Vector_lex___auto__1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__36;
static lean_once_cell_t l_Vector_lex___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__37;
static lean_once_cell_t l_Vector_lex___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__38;
static lean_once_cell_t l_Vector_lex___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__39;
static lean_once_cell_t l_Vector_lex___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__40;
static lean_once_cell_t l_Vector_lex___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__41;
static lean_once_cell_t l_Vector_lex___auto__1___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__42;
static lean_once_cell_t l_Vector_lex___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__43;
static lean_once_cell_t l_Vector_lex___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__44;
static lean_once_cell_t l_Vector_lex___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__45;
static lean_once_cell_t l_Vector_lex___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__46;
LEAN_EXPORT lean_object* l_Vector_lex___auto__1;
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object* v_inst_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Array_instDecidableEqImpl___redArg(v_inst_1_, v_x_2_, v_x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object* v_inst_5_, lean_object* v_x_6_, lean_object* v_x_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_instDecidableEqVector_decEq___redArg(v_inst_5_, v_x_6_, v_x_7_);
lean_dec_ref(v_x_7_);
lean_dec_ref(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object* v_00_u03b1_10_, lean_object* v_n_11_, lean_object* v_inst_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = l_Array_instDecidableEqImpl___redArg(v_inst_12_, v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object* v_00_u03b1_16_, lean_object* v_n_17_, lean_object* v_inst_18_, lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_instDecidableEqVector_decEq(v_00_u03b1_16_, v_n_17_, v_inst_18_, v_x_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_x_19_);
lean_dec(v_n_17_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object* v_inst_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = l_Array_instDecidableEqImpl___redArg(v_inst_23_, v_x_24_, v_x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object* v_inst_27_, lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_instDecidableEqVector___redArg(v_inst_27_, v_x_28_, v_x_29_);
lean_dec_ref(v_x_29_);
lean_dec_ref(v_x_28_);
v_r_31_ = lean_box(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object* v_00_u03b1_32_, lean_object* v_n_33_, lean_object* v_inst_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
uint8_t v___x_37_; 
v___x_37_ = l_Array_instDecidableEqImpl___redArg(v_inst_34_, v_x_35_, v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object* v_00_u03b1_38_, lean_object* v_n_39_, lean_object* v_inst_40_, lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_instDecidableEqVector(v_00_u03b1_38_, v_n_39_, v_inst_40_, v_x_41_, v_x_42_);
lean_dec_ref(v_x_42_);
lean_dec_ref(v_x_41_);
lean_dec(v_n_39_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object* v_xs_45_){
_start:
{
lean_inc_ref(v_xs_45_);
return v_xs_45_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object* v_xs_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Array_toVector___redArg(v_xs_46_);
lean_dec_ref(v_xs_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector(lean_object* v_00_u03b1_48_, lean_object* v_xs_49_){
_start:
{
lean_inc_ref(v_xs_49_);
return v_xs_49_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object* v_00_u03b1_50_, lean_object* v_xs_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Array_toVector(v_00_u03b1_50_, v_xs_51_);
lean_dec_ref(v_xs_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object* v_n_53_){
_start:
{
lean_inc(v_n_53_);
return v_n_53_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object* v_n_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Vector_size___redArg(v_n_54_);
lean_dec(v_n_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Vector_size(lean_object* v_00_u03b1_56_, lean_object* v_n_57_, lean_object* v_x_58_){
_start:
{
lean_inc(v_n_57_);
return v_n_57_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object* v_00_u03b1_59_, lean_object* v_n_60_, lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Vector_size(v_00_u03b1_59_, v_n_60_, v_x_61_);
lean_dec_ref(v_x_61_);
lean_dec(v_n_60_);
return v_res_62_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5));
v___x_122_ = l_String_toRawSubstring_x27(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18));
v___x_150_ = l_String_toRawSubstring_x27(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26(void){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Array_mkArray0___redArg();
return v___x_159_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27));
v___x_162_ = l_String_toRawSubstring_x27(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
lean_inc(v_x_171_);
v___x_175_ = l_Lean_Syntax_isOfKind(v_x_171_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_x_171_);
v___x_176_ = lean_box(1);
v___x_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
return v___x_177_;
}
else
{
lean_object* v_quotContext_178_; lean_object* v_currMacroScope_179_; lean_object* v_ref_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_elems_183_; uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_quotContext_178_ = lean_ctor_get(v_a_172_, 1);
v_currMacroScope_179_ = lean_ctor_get(v_a_172_, 2);
v_ref_180_ = lean_ctor_get(v_a_172_, 5);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_171_, v___x_181_);
lean_dec(v_x_171_);
v_elems_183_ = l_Lean_Syntax_getArgs(v___x_182_);
lean_dec(v___x_182_);
v___x_184_ = 0;
v___x_185_ = l_Lean_SourceInfo_fromRef(v_ref_180_, v___x_184_);
v___x_186_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
v___x_187_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
v___x_188_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8));
lean_inc_n(v_currMacroScope_179_, 3);
lean_inc_n(v_quotContext_178_, 3);
v___x_189_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_188_, v_currMacroScope_179_);
v___x_190_ = lean_box(0);
v___x_191_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12));
lean_inc_n(v___x_185_, 12);
v___x_192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_192_, 0, v___x_185_);
lean_ctor_set(v___x_192_, 1, v___x_187_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
lean_ctor_set(v___x_192_, 3, v___x_191_);
v___x_193_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_194_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16));
v___x_195_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_185_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
v___x_198_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20));
v___x_199_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_198_, v_currMacroScope_179_);
v___x_200_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_200_, 0, v___x_185_);
lean_ctor_set(v___x_200_, 1, v___x_197_);
lean_ctor_set(v___x_200_, 2, v___x_199_);
lean_ctor_set(v___x_200_, 3, v___x_190_);
v___x_201_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21));
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_185_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_183_);
v___x_204_ = lean_array_get_size(v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = l_Nat_reprFast(v___x_204_);
v___x_206_ = lean_box(2);
v___x_207_ = l_Lean_Syntax_mkNumLit(v___x_205_, v___x_206_);
v___x_208_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_185_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = l_Lean_Syntax_node5(v___x_185_, v___x_194_, v___x_196_, v___x_200_, v___x_202_, v___x_207_, v___x_209_);
v___x_211_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
v___x_212_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25));
v___x_213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_185_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_215_ = l_Array_append___redArg(v___x_214_, v_elems_183_);
lean_dec_ref(v_elems_183_);
v___x_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_216_, 0, v___x_185_);
lean_ctor_set(v___x_216_, 1, v___x_193_);
lean_ctor_set(v___x_216_, 2, v___x_215_);
v___x_217_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_185_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_Syntax_node3(v___x_185_, v___x_211_, v___x_213_, v___x_216_, v___x_218_);
v___x_220_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
v___x_221_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29));
v___x_222_ = l_Lean_addMacroScope(v_quotContext_178_, v___x_221_, v_currMacroScope_179_);
v___x_223_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31));
v___x_224_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_224_, 0, v___x_185_);
lean_ctor_set(v___x_224_, 1, v___x_220_);
lean_ctor_set(v___x_224_, 2, v___x_222_);
lean_ctor_set(v___x_224_, 3, v___x_223_);
v___x_225_ = l_Lean_Syntax_node3(v___x_185_, v___x_193_, v___x_210_, v___x_219_, v___x_224_);
v___x_226_ = l_Lean_Syntax_node2(v___x_185_, v___x_186_, v___x_192_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_a_173_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object* v_x_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(v_x_228_, v_a_229_, v_a_230_);
lean_dec_ref(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object* v_x_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
lean_inc(v_x_232_);
v___x_236_ = l_Lean_Syntax_isOfKind(v_x_232_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_a_234_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = l_Lean_Syntax_getArg(v_x_232_, v___x_239_);
lean_dec(v_x_232_);
v___x_241_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_240_);
v___x_242_ = l_Lean_Syntax_matchesNull(v___x_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v_a_234_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Lean_Syntax_getArg(v___x_240_, v___x_245_);
lean_dec(v___x_240_);
v___x_247_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
lean_inc(v___x_246_);
v___x_248_ = l_Lean_Syntax_isOfKind(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v___x_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v_a_234_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_251_ = l_Lean_Syntax_getArg(v___x_246_, v___x_239_);
lean_dec(v___x_246_);
v___x_252_ = l_Lean_Syntax_getArgs(v___x_251_);
lean_dec(v___x_251_);
v___x_253_ = 0;
v___x_254_ = l_Lean_SourceInfo_fromRef(v_a_233_, v___x_253_);
v___x_255_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
v___x_256_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
lean_inc_n(v___x_254_, 3);
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_254_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_259_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_260_ = l_Array_append___redArg(v___x_259_, v___x_252_);
lean_dec_ref(v___x_252_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v___x_254_);
lean_ctor_set(v___x_261_, 1, v___x_258_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
v___x_262_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__18));
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_254_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_Syntax_node3(v___x_254_, v___x_255_, v___x_257_, v___x_261_, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_234_);
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object* v_x_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Vector_unexpandMk(v_x_266_, v_a_267_, v_a_268_);
lean_dec(v_a_267_);
return v_res_269_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
v___x_276_ = lean_string_length(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Vector_Vector_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__2, &l_Vector_Vector_repr___redArg___closed__2_once, _init_l_Vector_Vector_repr___redArg___closed__2);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg(lean_object* v_inst_286_, lean_object* v_n_287_, lean_object* v_xs_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_nat_dec_eq(v_n_287_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v_x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_x_291_ = lean_alloc_closure((void*)(l_repr), 3, 2);
lean_closure_set(v_x_291_, 0, lean_box(0));
lean_closure_set(v_x_291_, 1, v_inst_286_);
v___x_292_ = lean_array_to_list(v_xs_288_);
v___x_293_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__1));
v___x_294_ = l_Std_Format_joinSep___redArg(v_x_291_, v___x_292_, v___x_293_);
v___x_295_ = lean_obj_once(&l_Vector_Vector_repr___redArg___closed__3, &l_Vector_Vector_repr___redArg___closed__3_once, _init_l_Vector_Vector_repr___redArg___closed__3);
v___x_296_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__4));
v___x_297_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
v___x_298_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__5));
v___x_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_295_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Std_Format_fill(v___x_300_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_xs_288_);
lean_dec_ref(v_inst_286_);
v___x_302_ = ((lean_object*)(l_Vector_Vector_repr___redArg___closed__7));
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___redArg___boxed(lean_object* v_inst_303_, lean_object* v_n_304_, lean_object* v_xs_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Vector_Vector_repr___redArg(v_inst_303_, v_n_304_, v_xs_305_);
lean_dec(v_n_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_n_309_, lean_object* v_xs_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Vector_Vector_repr___redArg(v_inst_308_, v_n_309_, v_xs_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_repr___boxed(lean_object* v_00_u03b1_312_, lean_object* v_inst_313_, lean_object* v_n_314_, lean_object* v_xs_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Vector_Vector_repr(v_00_u03b1_312_, v_inst_313_, v_n_314_, v_xs_315_);
lean_dec(v_n_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0(lean_object* v_inst_317_, lean_object* v_n_318_, lean_object* v_xs_319_, lean_object* v_x_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Vector_Vector_repr___redArg(v_inst_317_, v_n_318_, v_xs_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg___lam__0___boxed(lean_object* v_inst_322_, lean_object* v_n_323_, lean_object* v_xs_324_, lean_object* v_x_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Vector_Vector_instRepr___redArg___lam__0(v_inst_322_, v_n_323_, v_xs_324_, v_x_325_);
lean_dec(v_x_325_);
lean_dec(v_n_323_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr___redArg(lean_object* v_inst_327_, lean_object* v_n_328_){
_start:
{
lean_object* v___f_329_; 
v___f_329_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_329_, 0, v_inst_327_);
lean_closure_set(v___f_329_, 1, v_n_328_);
return v___f_329_;
}
}
LEAN_EXPORT lean_object* l_Vector_Vector_instRepr(lean_object* v_00_u03b1_330_, lean_object* v_inst_331_, lean_object* v_n_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Vector_Vector_instRepr___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_333_, 0, v_inst_331_);
lean_closure_set(v___f_333_, 1, v_n_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object* v_xs_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_array_to_list(v_xs_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList(lean_object* v_00_u03b1_336_, lean_object* v_n_337_, lean_object* v_xs_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_array_to_list(v_xs_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object* v_00_u03b1_340_, lean_object* v_n_341_, lean_object* v_xs_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Vector_toList(v_00_u03b1_340_, v_n_341_, v_xs_342_);
lean_dec(v_n_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object* v_mk_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_apply_2(v_mk_344_, v_x_345_, lean_box(0));
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object* v_00_u03b1_347_, lean_object* v_n_348_, lean_object* v_motive_349_, lean_object* v_mk_350_, lean_object* v_x_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_apply_2(v_mk_350_, v_x_351_, lean_box(0));
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object* v_00_u03b1_353_, lean_object* v_n_354_, lean_object* v_motive_355_, lean_object* v_mk_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Vector_elimAsArray(v_00_u03b1_353_, v_n_354_, v_motive_355_, v_mk_356_, v_x_357_);
lean_dec(v_n_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object* v_mk_359_, lean_object* v_x_360_){
_start:
{
lean_object* v_toList_361_; lean_object* v___x_362_; 
v_toList_361_ = lean_array_to_list(v_x_360_);
v___x_362_ = lean_apply_2(v_mk_359_, v_toList_361_, lean_box(0));
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object* v_00_u03b1_363_, lean_object* v_n_364_, lean_object* v_motive_365_, lean_object* v_mk_366_, lean_object* v_x_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Vector_elimAsList___redArg(v_mk_366_, v_x_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object* v_00_u03b1_369_, lean_object* v_n_370_, lean_object* v_motive_371_, lean_object* v_mk_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Vector_elimAsList(v_00_u03b1_369_, v_n_370_, v_motive_371_, v_mk_372_, v_x_373_);
lean_dec(v_n_370_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object* v_capacity_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_mk_empty_array_with_capacity(v_capacity_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Vector_emptyWithCapacity___redArg(v_capacity_377_);
lean_dec(v_capacity_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object* v_00_u03b1_379_, lean_object* v_capacity_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_mk_empty_array_with_capacity(v_capacity_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object* v_00_u03b1_382_, lean_object* v_capacity_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Vector_emptyWithCapacity(v_00_u03b1_382_, v_capacity_383_);
lean_dec(v_capacity_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object* v_n_385_, lean_object* v_v_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_mk_array(v_n_385_, v_v_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object* v_00_u03b1_388_, lean_object* v_n_389_, lean_object* v_v_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_mk_array(v_n_389_, v_v_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object* v_v_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_mk_empty_array_with_capacity(v___x_393_);
v___x_395_ = lean_array_push(v___x_394_, v_v_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object* v_00_u03b1_396_, lean_object* v_v_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_array_push(v___x_399_, v_v_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object* v_n_401_, lean_object* v_inst_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_mk_array(v_n_401_, v_inst_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object* v_00_u03b1_404_, lean_object* v_n_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_mk_array(v_n_405_, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object* v_xs_408_, lean_object* v_i_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = lean_array_fget_borrowed(v_xs_408_, v_i_409_);
lean_inc(v___x_410_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object* v_xs_411_, lean_object* v_i_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Vector_get___redArg(v_xs_411_, v_i_412_);
lean_dec(v_i_412_);
lean_dec_ref(v_xs_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Vector_get(lean_object* v_00_u03b1_414_, lean_object* v_n_415_, lean_object* v_xs_416_, lean_object* v_i_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_array_fget_borrowed(v_xs_416_, v_i_417_);
lean_inc(v___x_418_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object* v_00_u03b1_419_, lean_object* v_n_420_, lean_object* v_xs_421_, lean_object* v_i_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Vector_get(v_00_u03b1_419_, v_n_420_, v_xs_421_, v_i_422_);
lean_dec(v_i_422_);
lean_dec_ref(v_xs_421_);
lean_dec(v_n_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object* v_xs_424_, size_t v_i_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_array_uget_borrowed(v_xs_424_, v_i_425_);
lean_inc(v___x_426_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object* v_xs_427_, lean_object* v_i_428_){
_start:
{
size_t v_i_boxed_429_; lean_object* v_res_430_; 
v_i_boxed_429_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_res_430_ = l_Vector_uget___redArg(v_xs_427_, v_i_boxed_429_);
lean_dec_ref(v_xs_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget(lean_object* v_00_u03b1_431_, lean_object* v_n_432_, lean_object* v_xs_433_, size_t v_i_434_, lean_object* v_h_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = lean_array_uget_borrowed(v_xs_433_, v_i_434_);
lean_inc(v___x_436_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object* v_00_u03b1_437_, lean_object* v_n_438_, lean_object* v_xs_439_, lean_object* v_i_440_, lean_object* v_h_441_){
_start:
{
size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_443_ = l_Vector_uget(v_00_u03b1_437_, v_n_438_, v_xs_439_, v_i_boxed_442_, v_h_441_);
lean_dec_ref(v_xs_439_);
lean_dec(v_n_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0(lean_object* v_xs_444_, lean_object* v_i_445_, lean_object* v_h_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_array_fget_borrowed(v_xs_444_, v_i_445_);
lean_inc(v___x_447_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___lam__0___boxed(lean_object* v_xs_448_, lean_object* v_i_449_, lean_object* v_h_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Vector_instGetElemNatLt___redArg___lam__0(v_xs_448_, v_i_449_, v_h_450_);
lean_dec(v_i_449_);
lean_dec_ref(v_xs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg(){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___redArg___boxed(lean_object* v___dummy_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Vector_instGetElemNatLt___redArg();
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_457_, lean_object* v_n_458_){
_start:
{
lean_object* v___f_459_; 
v___f_459_ = ((lean_object*)(l_Vector_instGetElemNatLt___redArg___closed__0));
return v___f_459_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_460_, lean_object* v_n_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Vector_instGetElemNatLt(v_00_u03b1_460_, v_n_461_);
lean_dec(v_n_461_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object* v_inst_463_, lean_object* v_xs_464_, lean_object* v_a_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = l_Array_contains___redArg(v_inst_463_, v_xs_464_, v_a_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_467_, lean_object* v_xs_468_, lean_object* v_a_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Vector_contains___redArg(v_inst_467_, v_xs_468_, v_a_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains(lean_object* v_00_u03b1_472_, lean_object* v_n_473_, lean_object* v_inst_474_, lean_object* v_xs_475_, lean_object* v_a_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = l_Array_contains___redArg(v_inst_474_, v_xs_475_, v_a_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_478_, lean_object* v_n_479_, lean_object* v_inst_480_, lean_object* v_xs_481_, lean_object* v_a_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Vector_contains(v_00_u03b1_478_, v_n_479_, v_inst_480_, v_xs_481_, v_a_482_);
lean_dec(v_n_479_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg(){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = lean_box(0);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___redArg___boxed(lean_object* v___dummy_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Vector_instMembership___redArg();
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_489_, lean_object* v_n_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(0);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_492_, lean_object* v_n_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Vector_instMembership(v_00_u03b1_492_, v_n_493_);
lean_dec(v_n_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_495_, lean_object* v_i_496_, lean_object* v_default_497_){
_start:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = lean_array_get_size(v_xs_495_);
v___x_499_ = lean_nat_dec_lt(v_i_496_, v___x_498_);
if (v___x_499_ == 0)
{
lean_inc(v_default_497_);
return v_default_497_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = lean_array_fget_borrowed(v_xs_495_, v_i_496_);
lean_inc(v___x_500_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_501_, lean_object* v_i_502_, lean_object* v_default_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Vector_getD___redArg(v_xs_501_, v_i_502_, v_default_503_);
lean_dec(v_default_503_);
lean_dec(v_i_502_);
lean_dec_ref(v_xs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_505_, lean_object* v_n_506_, lean_object* v_xs_507_, lean_object* v_i_508_, lean_object* v_default_509_){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = lean_array_get_size(v_xs_507_);
v___x_511_ = lean_nat_dec_lt(v_i_508_, v___x_510_);
if (v___x_511_ == 0)
{
lean_inc(v_default_509_);
return v_default_509_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = lean_array_fget_borrowed(v_xs_507_, v_i_508_);
lean_inc(v___x_512_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_513_, lean_object* v_n_514_, lean_object* v_xs_515_, lean_object* v_i_516_, lean_object* v_default_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Vector_getD(v_00_u03b1_513_, v_n_514_, v_xs_515_, v_i_516_, v_default_517_);
lean_dec(v_default_517_);
lean_dec(v_i_516_);
lean_dec_ref(v_xs_515_);
lean_dec(v_n_514_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_519_, lean_object* v_xs_520_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_array_get_size(v_xs_520_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_sub(v___x_521_, v___x_522_);
v___x_524_ = lean_array_get_borrowed(v_inst_519_, v_xs_520_, v___x_523_);
lean_dec(v___x_523_);
lean_inc(v___x_524_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_525_, lean_object* v_xs_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Vector_back_x21___redArg(v_inst_525_, v_xs_526_);
lean_dec_ref(v_xs_526_);
lean_dec(v_inst_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_528_, lean_object* v_n_529_, lean_object* v_inst_530_, lean_object* v_xs_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_532_ = lean_array_get_size(v_xs_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_array_get_borrowed(v_inst_530_, v_xs_531_, v___x_534_);
lean_dec(v___x_534_);
lean_inc(v___x_535_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_536_, lean_object* v_n_537_, lean_object* v_inst_538_, lean_object* v_xs_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Vector_back_x21(v_00_u03b1_536_, v_n_537_, v_inst_538_, v_xs_539_);
lean_dec_ref(v_xs_539_);
lean_dec(v_inst_538_);
lean_dec(v_n_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_542_ = lean_array_get_size(v_xs_541_);
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_nat_dec_lt(v___x_544_, v___x_542_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec(v___x_544_);
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_array_fget_borrowed(v_xs_541_, v___x_544_);
lean_dec(v___x_544_);
lean_inc(v___x_547_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Vector_back_x3f___redArg(v_xs_549_);
lean_dec_ref(v_xs_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_551_, lean_object* v_n_552_, lean_object* v_xs_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_array_get_size(v_xs_553_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_sub(v___x_554_, v___x_555_);
v___x_557_ = lean_nat_dec_lt(v___x_556_, v___x_554_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v___x_556_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_array_fget_borrowed(v_xs_553_, v___x_556_);
lean_dec(v___x_556_);
lean_inc(v___x_559_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_561_, lean_object* v_n_562_, lean_object* v_xs_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Vector_back_x3f(v_00_u03b1_561_, v_n_562_, v_xs_563_);
lean_dec_ref(v_xs_563_);
lean_dec(v_n_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_565_, lean_object* v_xs_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_sub(v_n_565_, v___x_567_);
v___x_569_ = lean_array_fget_borrowed(v_xs_566_, v___x_568_);
lean_dec(v___x_568_);
lean_inc(v___x_569_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_570_, lean_object* v_xs_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Vector_back___redArg(v_n_570_, v_xs_571_);
lean_dec_ref(v_xs_571_);
lean_dec(v_n_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_573_, lean_object* v_00_u03b1_574_, lean_object* v_inst_575_, lean_object* v_xs_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(1u);
v___x_578_ = lean_nat_sub(v_n_573_, v___x_577_);
v___x_579_ = lean_array_fget_borrowed(v_xs_576_, v___x_578_);
lean_dec(v___x_578_);
lean_inc(v___x_579_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_580_, lean_object* v_00_u03b1_581_, lean_object* v_inst_582_, lean_object* v_xs_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Vector_back(v_n_580_, v_00_u03b1_581_, v_inst_582_, v_xs_583_);
lean_dec_ref(v_xs_583_);
lean_dec(v_n_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_array_fget_borrowed(v_xs_585_, v___x_586_);
lean_inc(v___x_587_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Vector_head___redArg(v_xs_588_);
lean_dec_ref(v_xs_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_590_, lean_object* v_00_u03b1_591_, lean_object* v_inst_592_, lean_object* v_xs_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_array_fget_borrowed(v_xs_593_, v___x_594_);
lean_inc(v___x_595_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_596_, lean_object* v_00_u03b1_597_, lean_object* v_inst_598_, lean_object* v_xs_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Vector_head(v_n_596_, v_00_u03b1_597_, v_inst_598_, v_xs_599_);
lean_dec_ref(v_xs_599_);
lean_dec(v_n_596_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_array_push(v_xs_601_, v_x_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_604_, lean_object* v_n_605_, lean_object* v_xs_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_push(v_xs_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_609_, lean_object* v_n_610_, lean_object* v_xs_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Vector_push(v_00_u03b1_609_, v_n_610_, v_xs_611_, v_x_612_);
lean_dec(v_n_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_pop(v_xs_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_616_, lean_object* v_n_617_, lean_object* v_xs_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_pop(v_xs_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_620_, lean_object* v_n_621_, lean_object* v_xs_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Vector_pop(v_00_u03b1_620_, v_n_621_, v_xs_622_);
lean_dec(v_n_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___redArg(lean_object* v_xs_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_array_mark_linear(v_xs_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear(lean_object* v_00_u03b1_626_, lean_object* v_n_627_, lean_object* v_xs_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_array_mark_linear(v_xs_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Vector_markLinear___boxed(lean_object* v_00_u03b1_630_, lean_object* v_n_631_, lean_object* v_xs_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Vector_markLinear(v_00_u03b1_630_, v_n_631_, v_xs_632_);
lean_dec(v_n_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg(lean_object* v_xs_634_, lean_object* v_ys_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = lean_array_propagate_mark(v_xs_634_, v_ys_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___redArg___boxed(lean_object* v_xs_637_, lean_object* v_ys_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Vector_propagateMark___redArg(v_xs_637_, v_ys_638_);
lean_dec_ref(v_xs_637_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark(lean_object* v_n_640_, lean_object* v_m_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_xs_644_, lean_object* v_ys_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_propagate_mark(v_xs_644_, v_ys_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Vector_propagateMark___boxed(lean_object* v_n_647_, lean_object* v_m_648_, lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_xs_651_, lean_object* v_ys_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Vector_propagateMark(v_n_647_, v_m_648_, v_00_u03b1_649_, v_00_u03b2_650_, v_xs_651_, v_ys_652_);
lean_dec_ref(v_xs_651_);
lean_dec(v_m_648_);
lean_dec(v_n_647_);
return v_res_653_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_674_ = l_Lean_mkAtom(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_676_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_677_ = lean_array_push(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_679_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_680_ = lean_box(2);
v___x_681_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___x_679_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
return v___x_681_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_683_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_684_ = lean_array_push(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_686_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_687_ = lean_box(2);
v___x_688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
return v___x_688_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_690_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_691_ = lean_array_push(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_693_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_694_ = lean_box(2);
v___x_695_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
lean_ctor_set(v___x_695_, 2, v___x_692_);
return v___x_695_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_697_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_698_ = lean_array_push(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_700_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_701_ = lean_box(2);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_699_);
return v___x_702_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_704_, lean_object* v_i_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_array_fset(v_xs_704_, v_i_705_, v_x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_708_, lean_object* v_i_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Vector_set___redArg(v_xs_708_, v_i_709_, v_x_710_);
lean_dec(v_i_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_712_, lean_object* v_n_713_, lean_object* v_xs_714_, lean_object* v_i_715_, lean_object* v_x_716_, lean_object* v_h_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_array_fset(v_xs_714_, v_i_715_, v_x_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_719_, lean_object* v_n_720_, lean_object* v_xs_721_, lean_object* v_i_722_, lean_object* v_x_723_, lean_object* v_h_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Vector_set(v_00_u03b1_719_, v_n_720_, v_xs_721_, v_i_722_, v_x_723_, v_h_724_);
lean_dec(v_i_722_);
lean_dec(v_n_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_726_, lean_object* v_i_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_array_get_size(v_xs_726_);
v___x_730_ = lean_nat_dec_lt(v_i_727_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v_x_728_);
return v_xs_726_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = lean_array_fset(v_xs_726_, v_i_727_, v_x_728_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_732_, lean_object* v_i_733_, lean_object* v_x_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Vector_setIfInBounds___redArg(v_xs_732_, v_i_733_, v_x_734_);
lean_dec(v_i_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_736_, lean_object* v_n_737_, lean_object* v_xs_738_, lean_object* v_i_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = lean_array_get_size(v_xs_738_);
v___x_742_ = lean_nat_dec_lt(v_i_739_, v___x_741_);
if (v___x_742_ == 0)
{
lean_dec(v_x_740_);
return v_xs_738_;
}
else
{
lean_object* v___x_743_; 
v___x_743_ = lean_array_fset(v_xs_738_, v_i_739_, v_x_740_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_744_, lean_object* v_n_745_, lean_object* v_xs_746_, lean_object* v_i_747_, lean_object* v_x_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Vector_setIfInBounds(v_00_u03b1_744_, v_n_745_, v_xs_746_, v_i_747_, v_x_748_);
lean_dec(v_i_747_);
lean_dec(v_n_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_750_, lean_object* v_i_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_set(v_xs_750_, v_i_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_754_, lean_object* v_i_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Vector_set_x21___redArg(v_xs_754_, v_i_755_, v_x_756_);
lean_dec(v_i_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_758_, lean_object* v_n_759_, lean_object* v_xs_760_, lean_object* v_i_761_, lean_object* v_x_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_array_set(v_xs_760_, v_i_761_, v_x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_764_, lean_object* v_n_765_, lean_object* v_xs_766_, lean_object* v_i_767_, lean_object* v_x_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Vector_set_x21(v_00_u03b1_764_, v_n_765_, v_xs_766_, v_i_767_, v_x_768_);
lean_dec(v_i_767_);
lean_dec(v_n_765_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_770_, lean_object* v_f_771_, lean_object* v_b_772_, lean_object* v_xs_773_){
_start:
{
lean_object* v_toApplicative_774_; lean_object* v_toPure_775_; lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_770_, 0);
v_toPure_775_ = lean_ctor_get(v_toApplicative_774_, 1);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_array_get_size(v_xs_773_);
v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_inc(v_toPure_775_);
lean_dec_ref(v_xs_773_);
lean_dec(v_f_771_);
lean_dec_ref(v_inst_770_);
v___x_779_ = lean_apply_2(v_toPure_775_, lean_box(0), v_b_772_);
return v___x_779_;
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_777_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_770_, v_f_771_, v_xs_773_, v___x_780_, v___x_781_, v_b_772_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_783_, lean_object* v_00_u03b2_784_, lean_object* v_00_u03b1_785_, lean_object* v_n_786_, lean_object* v_inst_787_, lean_object* v_f_788_, lean_object* v_b_789_, lean_object* v_xs_790_){
_start:
{
lean_object* v_toApplicative_791_; lean_object* v_toPure_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_toApplicative_791_ = lean_ctor_get(v_inst_787_, 0);
v_toPure_792_ = lean_ctor_get(v_toApplicative_791_, 1);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_array_get_size(v_xs_790_);
v___x_795_ = lean_nat_dec_lt(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
lean_inc(v_toPure_792_);
lean_dec_ref(v_xs_790_);
lean_dec(v_f_788_);
lean_dec_ref(v_inst_787_);
v___x_796_ = lean_apply_2(v_toPure_792_, lean_box(0), v_b_789_);
return v___x_796_;
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_of_nat(v___x_794_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_787_, v_f_788_, v_xs_790_, v___x_797_, v___x_798_, v_b_789_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_800_, lean_object* v_00_u03b2_801_, lean_object* v_00_u03b1_802_, lean_object* v_n_803_, lean_object* v_inst_804_, lean_object* v_f_805_, lean_object* v_b_806_, lean_object* v_xs_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Vector_foldlM(v_m_800_, v_00_u03b2_801_, v_00_u03b1_802_, v_n_803_, v_inst_804_, v_f_805_, v_b_806_, v_xs_807_);
lean_dec(v_n_803_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_809_, lean_object* v_f_810_, lean_object* v_b_811_, lean_object* v_xs_812_){
_start:
{
lean_object* v_toApplicative_813_; lean_object* v_toPure_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_toApplicative_813_ = lean_ctor_get(v_inst_809_, 0);
v_toPure_814_ = lean_ctor_get(v_toApplicative_813_, 1);
v___x_815_ = lean_array_get_size(v_xs_812_);
v___x_816_ = lean_unsigned_to_nat(0u);
v___x_817_ = lean_nat_dec_lt(v___x_816_, v___x_815_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
lean_inc(v_toPure_814_);
lean_dec_ref(v_xs_812_);
lean_dec(v_f_810_);
lean_dec_ref(v_inst_809_);
v___x_818_ = lean_apply_2(v_toPure_814_, lean_box(0), v_b_811_);
return v___x_818_;
}
else
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v___x_819_ = lean_usize_of_nat(v___x_815_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_809_, v_f_810_, v_xs_812_, v___x_819_, v___x_820_, v_b_811_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_822_, lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_n_825_, lean_object* v_inst_826_, lean_object* v_f_827_, lean_object* v_b_828_, lean_object* v_xs_829_){
_start:
{
lean_object* v_toApplicative_830_; lean_object* v_toPure_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_toApplicative_830_ = lean_ctor_get(v_inst_826_, 0);
v_toPure_831_ = lean_ctor_get(v_toApplicative_830_, 1);
v___x_832_ = lean_array_get_size(v_xs_829_);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_nat_dec_lt(v___x_833_, v___x_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
lean_inc(v_toPure_831_);
lean_dec_ref(v_xs_829_);
lean_dec(v_f_827_);
lean_dec_ref(v_inst_826_);
v___x_835_ = lean_apply_2(v_toPure_831_, lean_box(0), v_b_828_);
return v___x_835_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_usize_of_nat(v___x_832_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_826_, v_f_827_, v_xs_829_, v___x_836_, v___x_837_, v_b_828_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_839_, lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_n_842_, lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_b_845_, lean_object* v_xs_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Vector_foldrM(v_m_839_, v_00_u03b1_840_, v_00_u03b2_841_, v_n_842_, v_inst_843_, v_f_844_, v_b_845_, v_xs_846_);
lean_dec(v_n_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_848_, lean_object* v_x1_849_, lean_object* v_x2_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_apply_2(v_f_848_, v_x1_849_, v_x2_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_871_, lean_object* v_b_872_, lean_object* v_xs_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_array_get_size(v_xs_873_);
v___x_876_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_877_ = lean_nat_dec_lt(v___x_874_, v___x_875_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_xs_873_);
lean_dec(v_f_871_);
return v_b_872_;
}
else
{
lean_object* v___f_878_; size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; 
v___f_878_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_878_, 0, v_f_871_);
v___x_879_ = ((size_t)0ULL);
v___x_880_ = lean_usize_of_nat(v___x_875_);
v___x_881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_876_, v___f_878_, v_xs_873_, v___x_879_, v___x_880_, v_b_872_);
return v___x_881_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_882_, lean_object* v_00_u03b1_883_, lean_object* v_n_884_, lean_object* v_f_885_, lean_object* v_b_886_, lean_object* v_xs_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v_xs_887_);
v___x_890_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_891_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_891_ == 0)
{
lean_dec_ref(v_xs_887_);
lean_dec(v_f_885_);
return v_b_886_;
}
else
{
lean_object* v___f_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v___f_892_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_892_, 0, v_f_885_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = lean_usize_of_nat(v___x_889_);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_890_, v___f_892_, v_xs_887_, v___x_893_, v___x_894_, v_b_886_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_896_, lean_object* v_00_u03b1_897_, lean_object* v_n_898_, lean_object* v_f_899_, lean_object* v_b_900_, lean_object* v_xs_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Vector_foldl(v_00_u03b2_896_, v_00_u03b1_897_, v_n_898_, v_f_899_, v_b_900_, v_xs_901_);
lean_dec(v_n_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_903_, lean_object* v_b_904_, lean_object* v_xs_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_906_ = lean_array_get_size(v_xs_905_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_909_ = lean_nat_dec_lt(v___x_907_, v___x_906_);
if (v___x_909_ == 0)
{
lean_dec_ref(v_xs_905_);
lean_dec(v_f_903_);
return v_b_904_;
}
else
{
lean_object* v___f_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___f_910_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_910_, 0, v_f_903_);
v___x_911_ = lean_usize_of_nat(v___x_906_);
v___x_912_ = ((size_t)0ULL);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_908_, v___f_910_, v_xs_905_, v___x_911_, v___x_912_, v_b_904_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_n_916_, lean_object* v_f_917_, lean_object* v_b_918_, lean_object* v_xs_919_){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_920_ = lean_array_get_size(v_xs_919_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_923_ = lean_nat_dec_lt(v___x_921_, v___x_920_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_xs_919_);
lean_dec(v_f_917_);
return v_b_918_;
}
else
{
lean_object* v___f_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___f_924_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_924_, 0, v_f_917_);
v___x_925_ = lean_usize_of_nat(v___x_920_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_922_, v___f_924_, v_xs_919_, v___x_925_, v___x_926_, v_b_918_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_n_930_, lean_object* v_f_931_, lean_object* v_b_932_, lean_object* v_xs_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Vector_foldr(v_00_u03b1_928_, v_00_u03b2_929_, v_n_930_, v_f_931_, v_b_932_, v_xs_933_);
lean_dec(v_n_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_935_, lean_object* v_ys_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Array_append___redArg(v_xs_935_, v_ys_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_938_, lean_object* v_ys_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Vector_append___redArg(v_xs_938_, v_ys_939_);
lean_dec_ref(v_ys_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_941_, lean_object* v_n_942_, lean_object* v_m_943_, lean_object* v_xs_944_, lean_object* v_ys_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Array_append___redArg(v_xs_944_, v_ys_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_947_, lean_object* v_n_948_, lean_object* v_m_949_, lean_object* v_xs_950_, lean_object* v_ys_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Vector_append(v_00_u03b1_947_, v_n_948_, v_m_949_, v_xs_950_, v_ys_951_);
lean_dec_ref(v_ys_951_);
lean_dec(v_m_949_);
lean_dec(v_n_948_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_953_, lean_object* v_m_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_955_, 0, lean_box(0));
lean_closure_set(v___x_955_, 1, v_n_953_);
lean_closure_set(v___x_955_, 2, v_m_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_956_, lean_object* v_n_957_, lean_object* v_m_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_959_, 0, lean_box(0));
lean_closure_set(v___x_959_, 1, v_n_957_);
lean_closure_set(v___x_959_, 2, v_m_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_960_){
_start:
{
lean_inc_ref(v_xs_960_);
return v_xs_960_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Vector_cast___redArg(v_xs_961_);
lean_dec_ref(v_xs_961_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_963_, lean_object* v_m_964_, lean_object* v_00_u03b1_965_, lean_object* v_h_966_, lean_object* v_xs_967_){
_start:
{
lean_inc_ref(v_xs_967_);
return v_xs_967_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_968_, lean_object* v_m_969_, lean_object* v_00_u03b1_970_, lean_object* v_h_971_, lean_object* v_xs_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Vector_cast(v_n_968_, v_m_969_, v_00_u03b1_970_, v_h_971_, v_xs_972_);
lean_dec_ref(v_xs_972_);
lean_dec(v_m_969_);
lean_dec(v_n_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_974_, lean_object* v_start_975_, lean_object* v_stop_976_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Array_extract___redArg(v_xs_974_, v_start_975_, v_stop_976_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_978_, lean_object* v_start_979_, lean_object* v_stop_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Vector_extract___redArg(v_xs_978_, v_start_979_, v_stop_980_);
lean_dec_ref(v_xs_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_982_, lean_object* v_n_983_, lean_object* v_xs_984_, lean_object* v_start_985_, lean_object* v_stop_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Array_extract___redArg(v_xs_984_, v_start_985_, v_stop_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_988_, lean_object* v_n_989_, lean_object* v_xs_990_, lean_object* v_start_991_, lean_object* v_stop_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Vector_extract(v_00_u03b1_988_, v_n_989_, v_xs_990_, v_start_991_, v_stop_992_);
lean_dec_ref(v_xs_990_);
lean_dec(v_n_989_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_994_, lean_object* v_xs_995_, lean_object* v_i_996_){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = l_Array_extract___redArg(v_xs_995_, v___x_997_, v_i_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_999_, lean_object* v_xs_1000_, lean_object* v_i_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Vector_take___redArg(v_n_999_, v_xs_1000_, v_i_1001_);
lean_dec_ref(v_xs_1000_);
lean_dec(v_n_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1003_, lean_object* v_n_1004_, lean_object* v_xs_1005_, lean_object* v_i_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = l_Array_extract___redArg(v_xs_1005_, v___x_1007_, v_i_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1009_, lean_object* v_n_1010_, lean_object* v_xs_1011_, lean_object* v_i_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Vector_take(v_00_u03b1_1009_, v_n_1010_, v_xs_1011_, v_i_1012_);
lean_dec_ref(v_xs_1011_);
lean_dec(v_n_1010_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1014_, lean_object* v_i_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_xs_1014_);
v___x_1017_ = l_Array_extract___redArg(v_xs_1014_, v_i_1015_, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1018_, lean_object* v_i_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Vector_drop___redArg(v_xs_1018_, v_i_1019_);
lean_dec_ref(v_xs_1018_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1021_, lean_object* v_n_1022_, lean_object* v_xs_1023_, lean_object* v_i_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_array_get_size(v_xs_1023_);
v___x_1026_ = l_Array_extract___redArg(v_xs_1023_, v_i_1024_, v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_n_1028_, lean_object* v_xs_1029_, lean_object* v_i_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Vector_drop(v_00_u03b1_1027_, v_n_1028_, v_xs_1029_, v_i_1030_);
lean_dec_ref(v_xs_1029_);
lean_dec(v_n_1028_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1032_, lean_object* v_i_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Array_shrink___redArg(v_xs_1032_, v_i_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1035_, lean_object* v_i_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Vector_shrink___redArg(v_xs_1035_, v_i_1036_);
lean_dec(v_i_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1038_, lean_object* v_n_1039_, lean_object* v_xs_1040_, lean_object* v_i_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Array_shrink___redArg(v_xs_1040_, v_i_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_n_1044_, lean_object* v_xs_1045_, lean_object* v_i_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Vector_shrink(v_00_u03b1_1043_, v_n_1044_, v_xs_1045_, v_i_1046_);
lean_dec(v_i_1046_);
lean_dec(v_n_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_apply_1(v_f_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1051_, lean_object* v_xs_1052_){
_start:
{
lean_object* v___f_1053_; lean_object* v___x_1054_; size_t v_sz_1055_; size_t v___x_1056_; lean_object* v___x_1057_; 
v___f_1053_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1053_, 0, v_f_1051_);
v___x_1054_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1055_ = lean_array_size(v_xs_1052_);
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1054_, v___f_1053_, v_sz_1055_, v___x_1056_, v_xs_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1058_, lean_object* v_00_u03b2_1059_, lean_object* v_n_1060_, lean_object* v_f_1061_, lean_object* v_xs_1062_){
_start:
{
lean_object* v___f_1063_; lean_object* v___x_1064_; size_t v_sz_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___f_1063_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1063_, 0, v_f_1061_);
v___x_1064_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1065_ = lean_array_size(v_xs_1062_);
v___x_1066_ = ((size_t)0ULL);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1064_, v___f_1063_, v_sz_1065_, v___x_1066_, v_xs_1062_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_n_1070_, lean_object* v_f_1071_, lean_object* v_xs_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Vector_map(v_00_u03b1_1068_, v_00_u03b2_1069_, v_n_1070_, v_f_1071_, v_xs_1072_);
lean_dec(v_n_1070_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1074_, lean_object* v_i_1075_, lean_object* v_a_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = lean_apply_2(v_f_1074_, v_i_1075_, v_a_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1079_, lean_object* v_xs_1080_){
_start:
{
lean_object* v___f_1081_; lean_object* v___x_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v___f_1081_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1081_, 0, v_f_1079_);
v___x_1082_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1083_ = lean_array_size(v_xs_1080_);
v___x_1084_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1080_);
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1082_, v_xs_1080_, v___f_1081_, v_sz_1083_, v___x_1084_, v_xs_1080_);
lean_dec_ref(v_xs_1080_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_n_1088_, lean_object* v_f_1089_, lean_object* v_xs_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; size_t v_sz_1093_; size_t v___x_1094_; lean_object* v___x_1095_; 
v___f_1091_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1091_, 0, v_f_1089_);
v___x_1092_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1093_ = lean_array_size(v_xs_1090_);
v___x_1094_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1090_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v_xs_1090_, v___f_1091_, v_sz_1093_, v___x_1094_, v_xs_1090_);
lean_dec_ref(v_xs_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_n_1098_, lean_object* v_f_1099_, lean_object* v_xs_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Vector_mapIdx(v_00_u03b1_1096_, v_00_u03b2_1097_, v_n_1098_, v_f_1099_, v_xs_1100_);
lean_dec(v_n_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1102_, lean_object* v_x1_1103_, lean_object* v_x2_1104_, lean_object* v_x3_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_apply_3(v_f_1102_, v_x1_1103_, v_x2_1104_, lean_box(0));
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1107_, lean_object* v_f_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___f_1109_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1109_, 0, v_f_1108_);
v___x_1110_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1111_ = lean_array_size(v_xs_1107_);
v___x_1112_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1107_);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1110_, v_xs_1107_, v___f_1109_, v_sz_1111_, v___x_1112_, v_xs_1107_);
lean_dec_ref(v_xs_1107_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1114_, lean_object* v_n_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_xs_1117_, lean_object* v_f_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1119_, 0, v_f_1118_);
v___x_1120_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1121_ = lean_array_size(v_xs_1117_);
v___x_1122_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1117_);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v_xs_1117_, v___f_1119_, v_sz_1121_, v___x_1122_, v_xs_1117_);
lean_dec_ref(v_xs_1117_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1124_, lean_object* v_n_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_xs_1127_, lean_object* v_f_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Vector_mapFinIdx(v_00_u03b1_1124_, v_n_1125_, v_00_u03b2_1126_, v_xs_1127_, v_f_1128_);
lean_dec(v_n_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1130_, lean_object* v_acc_1131_, lean_object* v_n_1132_, lean_object* v_inst_1133_, lean_object* v_f_1134_, lean_object* v_xs_1135_, lean_object* v_____do__lift_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1130_, v_acc_1131_, v_n_1132_, v_inst_1133_, v_f_1134_, v_xs_1135_, v_____do__lift_1136_);
lean_dec(v_k_1130_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1138_, lean_object* v_inst_1139_, lean_object* v_f_1140_, lean_object* v_xs_1141_, lean_object* v_k_1142_, lean_object* v_acc_1143_){
_start:
{
lean_object* v_toApplicative_1144_; lean_object* v_toBind_1145_; lean_object* v_toPure_1146_; uint8_t v___x_1147_; 
v_toApplicative_1144_ = lean_ctor_get(v_inst_1139_, 0);
v_toBind_1145_ = lean_ctor_get(v_inst_1139_, 1);
lean_inc(v_toBind_1145_);
v_toPure_1146_ = lean_ctor_get(v_toApplicative_1144_, 1);
v___x_1147_ = lean_nat_dec_lt(v_k_1142_, v_n_1138_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_inc(v_toPure_1146_);
lean_dec(v_toBind_1145_);
lean_dec(v_k_1142_);
lean_dec_ref(v_xs_1141_);
lean_dec(v_f_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec(v_n_1138_);
v___x_1148_ = lean_apply_2(v_toPure_1146_, lean_box(0), v_acc_1143_);
return v___x_1148_;
}
else
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_inc_ref(v_xs_1141_);
lean_inc(v_f_1140_);
lean_inc(v_k_1142_);
v___f_1149_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1149_, 0, v_k_1142_);
lean_closure_set(v___f_1149_, 1, v_acc_1143_);
lean_closure_set(v___f_1149_, 2, v_n_1138_);
lean_closure_set(v___f_1149_, 3, v_inst_1139_);
lean_closure_set(v___f_1149_, 4, v_f_1140_);
lean_closure_set(v___f_1149_, 5, v_xs_1141_);
v___x_1150_ = lean_array_fget(v_xs_1141_, v_k_1142_);
lean_dec(v_k_1142_);
lean_dec_ref(v_xs_1141_);
v___x_1151_ = lean_apply_1(v_f_1140_, v___x_1150_);
v___x_1152_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v___x_1151_, v___f_1149_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1153_, lean_object* v_acc_1154_, lean_object* v_n_1155_, lean_object* v_inst_1156_, lean_object* v_f_1157_, lean_object* v_xs_1158_, lean_object* v_____do__lift_1159_){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_k_1153_, v___x_1160_);
v___x_1162_ = lean_array_push(v_acc_1154_, v_____do__lift_1159_);
v___x_1163_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1155_, v_inst_1156_, v_f_1157_, v_xs_1158_, v___x_1161_, v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1164_, lean_object* v_00_u03b1_1165_, lean_object* v_00_u03b2_1166_, lean_object* v_n_1167_, lean_object* v_inst_1168_, lean_object* v_f_1169_, lean_object* v_xs_1170_, lean_object* v_k_1171_, lean_object* v_h_1172_, lean_object* v_acc_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1167_, v_inst_1168_, v_f_1169_, v_xs_1170_, v_k_1171_, v_acc_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1177_, lean_object* v_inst_1178_, lean_object* v_f_1179_, lean_object* v_xs_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1183_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1177_, v_inst_1178_, v_f_1179_, v_xs_1180_, v___x_1181_, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1184_, lean_object* v_00_u03b1_1185_, lean_object* v_00_u03b2_1186_, lean_object* v_n_1187_, lean_object* v_inst_1188_, lean_object* v_f_1189_, lean_object* v_xs_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1193_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1187_, v_inst_1188_, v_f_1189_, v_xs_1190_, v___x_1191_, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_apply_1(v_f_1194_, v___y_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1198_, lean_object* v_xs_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_toApplicative_1201_; lean_object* v_toPure_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_toApplicative_1201_ = lean_ctor_get(v_inst_1198_, 0);
v_toPure_1202_ = lean_ctor_get(v_toApplicative_1201_, 1);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_array_get_size(v_xs_1199_);
v___x_1205_ = lean_box(0);
v___x_1206_ = lean_nat_dec_lt(v___x_1203_, v___x_1204_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_inc(v_toPure_1202_);
lean_dec(v_f_1200_);
lean_dec_ref(v_xs_1199_);
lean_dec_ref(v_inst_1198_);
v___x_1207_ = lean_apply_2(v_toPure_1202_, lean_box(0), v___x_1205_);
return v___x_1207_;
}
else
{
lean_object* v___f_1208_; size_t v___x_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1208_, 0, v_f_1200_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = lean_usize_of_nat(v___x_1204_);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1198_, v___f_1208_, v_xs_1199_, v___x_1209_, v___x_1210_, v___x_1205_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1212_, lean_object* v_00_u03b1_1213_, lean_object* v_n_1214_, lean_object* v_inst_1215_, lean_object* v_xs_1216_, lean_object* v_f_1217_){
_start:
{
lean_object* v_toApplicative_1218_; lean_object* v_toPure_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v_toApplicative_1218_ = lean_ctor_get(v_inst_1215_, 0);
v_toPure_1219_ = lean_ctor_get(v_toApplicative_1218_, 1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_array_get_size(v_xs_1216_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; 
lean_inc(v_toPure_1219_);
lean_dec(v_f_1217_);
lean_dec_ref(v_xs_1216_);
lean_dec_ref(v_inst_1215_);
v___x_1224_ = lean_apply_2(v_toPure_1219_, lean_box(0), v___x_1222_);
return v___x_1224_;
}
else
{
lean_object* v___f_1225_; size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___f_1225_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1225_, 0, v_f_1217_);
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1221_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1215_, v___f_1225_, v_xs_1216_, v___x_1226_, v___x_1227_, v___x_1222_);
return v___x_1228_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1229_, lean_object* v_00_u03b1_1230_, lean_object* v_n_1231_, lean_object* v_inst_1232_, lean_object* v_xs_1233_, lean_object* v_f_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Vector_forM(v_m_1229_, v_00_u03b1_1230_, v_n_1231_, v_inst_1232_, v_xs_1233_, v_f_1234_);
lean_dec(v_n_1231_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1236_, lean_object* v_acc_1237_, lean_object* v_n_1238_, lean_object* v_inst_1239_, lean_object* v_xs_1240_, lean_object* v_f_1241_, lean_object* v_____do__lift_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1236_, v_acc_1237_, v_n_1238_, v_inst_1239_, v_xs_1240_, v_f_1241_, v_____do__lift_1242_);
lean_dec_ref(v_____do__lift_1242_);
lean_dec(v_i_1236_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1244_, lean_object* v_inst_1245_, lean_object* v_xs_1246_, lean_object* v_f_1247_, lean_object* v_i_1248_, lean_object* v_acc_1249_){
_start:
{
lean_object* v_toApplicative_1250_; lean_object* v_toBind_1251_; lean_object* v_toPure_1252_; uint8_t v___x_1253_; 
v_toApplicative_1250_ = lean_ctor_get(v_inst_1245_, 0);
v_toBind_1251_ = lean_ctor_get(v_inst_1245_, 1);
lean_inc(v_toBind_1251_);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1250_, 1);
v___x_1253_ = lean_nat_dec_lt(v_i_1248_, v_n_1244_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_inc(v_toPure_1252_);
lean_dec(v_toBind_1251_);
lean_dec(v_i_1248_);
lean_dec(v_f_1247_);
lean_dec_ref(v_xs_1246_);
lean_dec_ref(v_inst_1245_);
lean_dec(v_n_1244_);
v___x_1254_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_acc_1249_);
return v___x_1254_;
}
else
{
lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_inc(v_f_1247_);
lean_inc_ref(v_xs_1246_);
lean_inc(v_i_1248_);
v___f_1255_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1255_, 0, v_i_1248_);
lean_closure_set(v___f_1255_, 1, v_acc_1249_);
lean_closure_set(v___f_1255_, 2, v_n_1244_);
lean_closure_set(v___f_1255_, 3, v_inst_1245_);
lean_closure_set(v___f_1255_, 4, v_xs_1246_);
lean_closure_set(v___f_1255_, 5, v_f_1247_);
v___x_1256_ = lean_array_fget(v_xs_1246_, v_i_1248_);
lean_dec(v_i_1248_);
lean_dec_ref(v_xs_1246_);
v___x_1257_ = lean_apply_1(v_f_1247_, v___x_1256_);
v___x_1258_ = lean_apply_4(v_toBind_1251_, lean_box(0), lean_box(0), v___x_1257_, v___f_1255_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1259_, lean_object* v_acc_1260_, lean_object* v_n_1261_, lean_object* v_inst_1262_, lean_object* v_xs_1263_, lean_object* v_f_1264_, lean_object* v_____do__lift_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_i_1259_, v___x_1266_);
v___x_1268_ = l_Array_append___redArg(v_acc_1260_, v_____do__lift_1265_);
v___x_1269_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1261_, v_inst_1262_, v_xs_1263_, v_f_1264_, v___x_1267_, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1270_, lean_object* v_00_u03b1_1271_, lean_object* v_n_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_k_1274_, lean_object* v_inst_1275_, lean_object* v_xs_1276_, lean_object* v_f_1277_, lean_object* v_i_1278_, lean_object* v_h_1279_, lean_object* v_acc_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1272_, v_inst_1275_, v_xs_1276_, v_f_1277_, v_i_1278_, v_acc_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1282_, lean_object* v_00_u03b1_1283_, lean_object* v_n_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_k_1286_, lean_object* v_inst_1287_, lean_object* v_xs_1288_, lean_object* v_f_1289_, lean_object* v_i_1290_, lean_object* v_h_1291_, lean_object* v_acc_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1282_, v_00_u03b1_1283_, v_n_1284_, v_00_u03b2_1285_, v_k_1286_, v_inst_1287_, v_xs_1288_, v_f_1289_, v_i_1290_, v_h_1291_, v_acc_1292_);
lean_dec(v_k_1286_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1294_, lean_object* v_inst_1295_, lean_object* v_xs_1296_, lean_object* v_f_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1300_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1294_, v_inst_1295_, v_xs_1296_, v_f_1297_, v___x_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1301_, lean_object* v_00_u03b1_1302_, lean_object* v_n_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_k_1305_, lean_object* v_inst_1306_, lean_object* v_xs_1307_, lean_object* v_f_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1311_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1303_, v_inst_1306_, v_xs_1307_, v_f_1308_, v___x_1309_, v___x_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1312_, lean_object* v_00_u03b1_1313_, lean_object* v_n_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_k_1316_, lean_object* v_inst_1317_, lean_object* v_xs_1318_, lean_object* v_f_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Vector_flatMapM(v_m_1312_, v_00_u03b1_1313_, v_n_1314_, v_00_u03b2_1315_, v_k_1316_, v_inst_1317_, v_xs_1318_, v_f_1319_);
lean_dec(v_k_1316_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1321_, lean_object* v_ys_1322_, lean_object* v_inst_1323_, lean_object* v_xs_1324_, lean_object* v_f_1325_, lean_object* v_n_1326_, lean_object* v_____do__lift_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1321_, v_ys_1322_, v_inst_1323_, v_xs_1324_, v_f_1325_, v_n_1326_, v_____do__lift_1327_);
lean_dec(v_n_1326_);
lean_dec(v_j_1321_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1329_, lean_object* v_xs_1330_, lean_object* v_f_1331_, lean_object* v_i_1332_, lean_object* v_j_1333_, lean_object* v_ys_1334_){
_start:
{
lean_object* v_toApplicative_1335_; lean_object* v_toBind_1336_; lean_object* v_toPure_1337_; lean_object* v_zero_1338_; uint8_t v_isZero_1339_; 
v_toApplicative_1335_ = lean_ctor_get(v_inst_1329_, 0);
v_toBind_1336_ = lean_ctor_get(v_inst_1329_, 1);
lean_inc(v_toBind_1336_);
v_toPure_1337_ = lean_ctor_get(v_toApplicative_1335_, 1);
v_zero_1338_ = lean_unsigned_to_nat(0u);
v_isZero_1339_ = lean_nat_dec_eq(v_i_1332_, v_zero_1338_);
if (v_isZero_1339_ == 1)
{
lean_object* v___x_1340_; 
lean_inc(v_toPure_1337_);
lean_dec(v_toBind_1336_);
lean_dec(v_j_1333_);
lean_dec(v_f_1331_);
lean_dec_ref(v_xs_1330_);
lean_dec_ref(v_inst_1329_);
v___x_1340_ = lean_apply_2(v_toPure_1337_, lean_box(0), v_ys_1334_);
return v___x_1340_;
}
else
{
lean_object* v_one_1341_; lean_object* v_n_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_one_1341_ = lean_unsigned_to_nat(1u);
v_n_1342_ = lean_nat_sub(v_i_1332_, v_one_1341_);
lean_inc(v_f_1331_);
lean_inc_ref(v_xs_1330_);
lean_inc(v_j_1333_);
v___f_1343_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1343_, 0, v_j_1333_);
lean_closure_set(v___f_1343_, 1, v_ys_1334_);
lean_closure_set(v___f_1343_, 2, v_inst_1329_);
lean_closure_set(v___f_1343_, 3, v_xs_1330_);
lean_closure_set(v___f_1343_, 4, v_f_1331_);
lean_closure_set(v___f_1343_, 5, v_n_1342_);
v___x_1344_ = lean_array_fget(v_xs_1330_, v_j_1333_);
lean_dec_ref(v_xs_1330_);
v___x_1345_ = lean_apply_3(v_f_1331_, v_j_1333_, v___x_1344_, lean_box(0));
v___x_1346_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1345_, v___f_1343_);
return v___x_1346_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1347_, lean_object* v_ys_1348_, lean_object* v_inst_1349_, lean_object* v_xs_1350_, lean_object* v_f_1351_, lean_object* v_n_1352_, lean_object* v_____do__lift_1353_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_unsigned_to_nat(1u);
v___x_1355_ = lean_nat_add(v_j_1347_, v___x_1354_);
v___x_1356_ = lean_array_push(v_ys_1348_, v_____do__lift_1353_);
v___x_1357_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1349_, v_xs_1350_, v_f_1351_, v_n_1352_, v___x_1355_, v___x_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1358_, lean_object* v_xs_1359_, lean_object* v_f_1360_, lean_object* v_i_1361_, lean_object* v_j_1362_, lean_object* v_ys_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1358_, v_xs_1359_, v_f_1360_, v_i_1361_, v_j_1362_, v_ys_1363_);
lean_dec(v_i_1361_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1365_, lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_m_1368_, lean_object* v_inst_1369_, lean_object* v_xs_1370_, lean_object* v_f_1371_, lean_object* v_i_1372_, lean_object* v_j_1373_, lean_object* v_inv_1374_, lean_object* v_ys_1375_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1369_, v_xs_1370_, v_f_1371_, v_i_1372_, v_j_1373_, v_ys_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1377_, lean_object* v_00_u03b1_1378_, lean_object* v_00_u03b2_1379_, lean_object* v_m_1380_, lean_object* v_inst_1381_, lean_object* v_xs_1382_, lean_object* v_f_1383_, lean_object* v_i_1384_, lean_object* v_j_1385_, lean_object* v_inv_1386_, lean_object* v_ys_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Vector_mapFinIdxM_map(v_n_1377_, v_00_u03b1_1378_, v_00_u03b2_1379_, v_m_1380_, v_inst_1381_, v_xs_1382_, v_f_1383_, v_i_1384_, v_j_1385_, v_inv_1386_, v_ys_1387_);
lean_dec(v_i_1384_);
lean_dec(v_n_1377_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1389_, lean_object* v_inst_1390_, lean_object* v_xs_1391_, lean_object* v_f_1392_){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1395_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1390_, v_xs_1391_, v_f_1392_, v_n_1389_, v___x_1393_, v___x_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1396_, lean_object* v_inst_1397_, lean_object* v_xs_1398_, lean_object* v_f_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Vector_mapFinIdxM___redArg(v_n_1396_, v_inst_1397_, v_xs_1398_, v_f_1399_);
lean_dec(v_n_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1401_, lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_m_1404_, lean_object* v_inst_1405_, lean_object* v_xs_1406_, lean_object* v_f_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1410_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1405_, v_xs_1406_, v_f_1407_, v_n_1401_, v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1411_, lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_m_1414_, lean_object* v_inst_1415_, lean_object* v_xs_1416_, lean_object* v_f_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Vector_mapFinIdxM(v_n_1411_, v_00_u03b1_1412_, v_00_u03b2_1413_, v_m_1414_, v_inst_1415_, v_xs_1416_, v_f_1417_);
lean_dec(v_n_1411_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1419_, lean_object* v_inst_1420_, lean_object* v_f_1421_, lean_object* v_xs_1422_){
_start:
{
lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___f_1423_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1423_, 0, v_f_1421_);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1426_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1420_, v_xs_1422_, v___f_1423_, v_n_1419_, v___x_1424_, v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1427_, lean_object* v_inst_1428_, lean_object* v_f_1429_, lean_object* v_xs_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Vector_mapIdxM___redArg(v_n_1427_, v_inst_1428_, v_f_1429_, v_xs_1430_);
lean_dec(v_n_1427_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1432_, lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_inst_1436_, lean_object* v_f_1437_, lean_object* v_xs_1438_){
_start:
{
lean_object* v___f_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___f_1439_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1439_, 0, v_f_1437_);
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1442_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1436_, v_xs_1438_, v___f_1439_, v_n_1432_, v___x_1440_, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1443_, lean_object* v_00_u03b1_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_m_1446_, lean_object* v_inst_1447_, lean_object* v_f_1448_, lean_object* v_xs_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Vector_mapIdxM(v_n_1443_, v_00_u03b1_1444_, v_00_u03b2_1445_, v_m_1446_, v_inst_1447_, v_f_1448_, v_xs_1449_);
lean_dec(v_n_1443_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1451_, lean_object* v_f_1452_, lean_object* v_xs_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1451_, v_f_1452_, v_xs_1453_, v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1456_, lean_object* v_n_1457_, lean_object* v_00_u03b1_1458_, lean_object* v_m_1459_, lean_object* v_inst_1460_, lean_object* v_f_1461_, lean_object* v_xs_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1460_, v_f_1461_, v_xs_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1465_, lean_object* v_n_1466_, lean_object* v_00_u03b1_1467_, lean_object* v_m_1468_, lean_object* v_inst_1469_, lean_object* v_f_1470_, lean_object* v_xs_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Vector_firstM(v_00_u03b2_1465_, v_n_1466_, v_00_u03b1_1467_, v_m_1468_, v_inst_1469_, v_f_1470_, v_xs_1471_);
lean_dec(v_n_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1473_){
_start:
{
lean_inc_ref(v_x_1473_);
return v_x_1473_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Vector_flatten___redArg___lam__0(v_x_1474_);
lean_dec_ref(v_x_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1480_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___f_1481_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1482_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1483_ = lean_array_size(v_xs_1480_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1482_, v___f_1481_, v_sz_1483_, v___x_1484_, v_xs_1480_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1488_ = lean_array_get_size(v___x_1485_);
v___x_1489_ = lean_nat_dec_lt(v___x_1486_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec(v___x_1485_);
return v___x_1487_;
}
else
{
lean_object* v___f_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v___f_1490_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1491_ = lean_usize_of_nat(v___x_1488_);
v___x_1492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1482_, v___f_1490_, v___x_1485_, v___x_1484_, v___x_1491_, v___x_1487_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1493_, lean_object* v_n_1494_, lean_object* v_m_1495_, lean_object* v_xs_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___x_1498_; size_t v_sz_1499_; size_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___f_1497_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1498_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1499_ = lean_array_size(v_xs_1496_);
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1498_, v___f_1497_, v_sz_1499_, v___x_1500_, v_xs_1496_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1504_ = lean_array_get_size(v___x_1501_);
v___x_1505_ = lean_nat_dec_lt(v___x_1502_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_dec(v___x_1501_);
return v___x_1503_;
}
else
{
lean_object* v___f_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
v___f_1506_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1507_ = lean_usize_of_nat(v___x_1504_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1498_, v___f_1506_, v___x_1501_, v___x_1500_, v___x_1507_, v___x_1503_);
return v___x_1508_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_n_1510_, lean_object* v_m_1511_, lean_object* v_xs_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Vector_flatten(v_00_u03b1_1509_, v_n_1510_, v_m_1511_, v_xs_1512_);
lean_dec(v_m_1511_);
lean_dec(v_n_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1514_, lean_object* v_x1_1515_, lean_object* v_x2_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_apply_1(v_f_1514_, v_x2_1516_);
v___x_1518_ = l_Array_append___redArg(v_x1_1515_, v___x_1517_);
lean_dec_ref(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1519_, lean_object* v_f_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1523_ = lean_array_get_size(v_xs_1519_);
v___x_1524_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1525_ = lean_nat_dec_lt(v___x_1521_, v___x_1523_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v_f_1520_);
lean_dec_ref(v_xs_1519_);
return v___x_1522_;
}
else
{
lean_object* v___f_1526_; size_t v___x_1527_; size_t v___x_1528_; lean_object* v___x_1529_; 
v___f_1526_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1526_, 0, v_f_1520_);
v___x_1527_ = ((size_t)0ULL);
v___x_1528_ = lean_usize_of_nat(v___x_1523_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1524_, v___f_1526_, v_xs_1519_, v___x_1527_, v___x_1528_, v___x_1522_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1530_, lean_object* v_n_1531_, lean_object* v_00_u03b2_1532_, lean_object* v_m_1533_, lean_object* v_xs_1534_, lean_object* v_f_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1538_ = lean_array_get_size(v_xs_1534_);
v___x_1539_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1540_ = lean_nat_dec_lt(v___x_1536_, v___x_1538_);
if (v___x_1540_ == 0)
{
lean_dec_ref(v_f_1535_);
lean_dec_ref(v_xs_1534_);
return v___x_1537_;
}
else
{
lean_object* v___f_1541_; size_t v___x_1542_; size_t v___x_1543_; lean_object* v___x_1544_; 
v___f_1541_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1541_, 0, v_f_1535_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = lean_usize_of_nat(v___x_1538_);
v___x_1544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1539_, v___f_1541_, v_xs_1534_, v___x_1542_, v___x_1543_, v___x_1537_);
return v___x_1544_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1545_, lean_object* v_n_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_m_1548_, lean_object* v_xs_1549_, lean_object* v_f_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Vector_flatMap(v_00_u03b1_1545_, v_n_1546_, v_00_u03b2_1547_, v_m_1548_, v_xs_1549_, v_f_1550_);
lean_dec(v_m_1548_);
lean_dec(v_n_1546_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Array_zipIdx___redArg(v_xs_1552_, v_k_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Vector_zipIdx___redArg(v_xs_1555_, v_k_1556_);
lean_dec(v_k_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1558_, lean_object* v_n_1559_, lean_object* v_xs_1560_, lean_object* v_k_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Array_zipIdx___redArg(v_xs_1560_, v_k_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_n_1564_, lean_object* v_xs_1565_, lean_object* v_k_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Vector_zipIdx(v_00_u03b1_1563_, v_n_1564_, v_xs_1565_, v_k_1566_);
lean_dec(v_k_1566_);
lean_dec(v_n_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1568_, lean_object* v_bs_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Array_zip___redArg(v_as_1568_, v_bs_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1571_, lean_object* v_bs_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Vector_zip___redArg(v_as_1571_, v_bs_1572_);
lean_dec_ref(v_bs_1572_);
lean_dec_ref(v_as_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1574_, lean_object* v_n_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_as_1577_, lean_object* v_bs_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Array_zip___redArg(v_as_1577_, v_bs_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1580_, lean_object* v_n_1581_, lean_object* v_00_u03b2_1582_, lean_object* v_as_1583_, lean_object* v_bs_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Vector_zip(v_00_u03b1_1580_, v_n_1581_, v_00_u03b2_1582_, v_as_1583_, v_bs_1584_);
lean_dec_ref(v_bs_1584_);
lean_dec_ref(v_as_1583_);
lean_dec(v_n_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1586_, lean_object* v_as_1587_, lean_object* v_bs_1588_){
_start:
{
lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___f_1589_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1589_, 0, v_f_1586_);
v___x_1590_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1593_ = l_Array_zipWithMAux___redArg(v___x_1590_, v_as_1587_, v_bs_1588_, v___f_1589_, v___x_1591_, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_00_u03c6_1596_, lean_object* v_n_1597_, lean_object* v_f_1598_, lean_object* v_as_1599_, lean_object* v_bs_1600_){
_start:
{
lean_object* v___f_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___f_1601_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1601_, 0, v_f_1598_);
v___x_1602_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1605_ = l_Array_zipWithMAux___redArg(v___x_1602_, v_as_1599_, v_bs_1600_, v___f_1601_, v___x_1603_, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_00_u03b2_1607_, lean_object* v_00_u03c6_1608_, lean_object* v_n_1609_, lean_object* v_f_1610_, lean_object* v_as_1611_, lean_object* v_bs_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Vector_zipWith(v_00_u03b1_1606_, v_00_u03b2_1607_, v_00_u03c6_1608_, v_n_1609_, v_f_1610_, v_as_1611_, v_bs_1612_);
lean_dec(v_n_1609_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
v___x_1615_ = l_Array_unzip___redArg(v_xs_1614_);
v_fst_1616_ = lean_ctor_get(v___x_1615_, 0);
v_snd_1617_ = lean_ctor_get(v___x_1615_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1615_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snd_1617_);
lean_inc(v_fst_1616_);
lean_dec(v___x_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_fst_1616_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_snd_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Vector_unzip___redArg(v_xs_1625_);
lean_dec_ref(v_xs_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_n_1629_, lean_object* v_xs_1630_){
_start:
{
lean_object* v___x_1631_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v___x_1631_ = l_Array_unzip___redArg(v_xs_1630_);
v_fst_1632_ = lean_ctor_get(v___x_1631_, 0);
v_snd_1633_ = lean_ctor_get(v___x_1631_, 1);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1631_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_snd_1633_);
lean_inc(v_fst_1632_);
lean_dec(v___x_1631_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_fst_1632_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_snd_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_n_1643_, lean_object* v_xs_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Vector_unzip(v_00_u03b1_1641_, v_00_u03b2_1642_, v_n_1643_, v_xs_1644_);
lean_dec_ref(v_xs_1644_);
lean_dec(v_n_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1646_, lean_object* v_f_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Array_ofFn___redArg(v_n_1646_, v_f_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1649_, lean_object* v_00_u03b1_1650_, lean_object* v_f_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Array_ofFn___redArg(v_n_1649_, v_f_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1653_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1655_, lean_object* v_i_1656_, lean_object* v_j_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_fswap(v_xs_1655_, v_i_1656_, v_j_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1659_, lean_object* v_i_1660_, lean_object* v_j_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Vector_swap___redArg(v_xs_1659_, v_i_1660_, v_j_1661_);
lean_dec(v_j_1661_);
lean_dec(v_i_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1663_, lean_object* v_n_1664_, lean_object* v_xs_1665_, lean_object* v_i_1666_, lean_object* v_j_1667_, lean_object* v_hi_1668_, lean_object* v_hj_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_array_fswap(v_xs_1665_, v_i_1666_, v_j_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1671_, lean_object* v_n_1672_, lean_object* v_xs_1673_, lean_object* v_i_1674_, lean_object* v_j_1675_, lean_object* v_hi_1676_, lean_object* v_hj_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Vector_swap(v_00_u03b1_1671_, v_n_1672_, v_xs_1673_, v_i_1674_, v_j_1675_, v_hi_1676_, v_hj_1677_);
lean_dec(v_j_1675_);
lean_dec(v_i_1674_);
lean_dec(v_n_1672_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1679_, lean_object* v_i_1680_, lean_object* v_j_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_array_swap(v_xs_1679_, v_i_1680_, v_j_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1683_, lean_object* v_i_1684_, lean_object* v_j_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Vector_swapIfInBounds___redArg(v_xs_1683_, v_i_1684_, v_j_1685_);
lean_dec(v_j_1685_);
lean_dec(v_i_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1687_, lean_object* v_n_1688_, lean_object* v_xs_1689_, lean_object* v_i_1690_, lean_object* v_j_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_array_swap(v_xs_1689_, v_i_1690_, v_j_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_n_1694_, lean_object* v_xs_1695_, lean_object* v_i_1696_, lean_object* v_j_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Vector_swapIfInBounds(v_00_u03b1_1693_, v_n_1694_, v_xs_1695_, v_i_1696_, v_j_1697_);
lean_dec(v_j_1697_);
lean_dec(v_i_1696_);
lean_dec(v_n_1694_);
return v_res_1698_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1700_, lean_object* v_i_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v_e_1703_; lean_object* v_xs_x27_1704_; lean_object* v___x_1705_; 
v_e_1703_ = lean_array_fget(v_xs_1700_, v_i_1701_);
v_xs_x27_1704_ = lean_array_fset(v_xs_1700_, v_i_1701_, v_x_1702_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_e_1703_);
lean_ctor_set(v___x_1705_, 1, v_xs_x27_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1706_, lean_object* v_i_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Vector_swapAt___redArg(v_xs_1706_, v_i_1707_, v_x_1708_);
lean_dec(v_i_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1710_, lean_object* v_n_1711_, lean_object* v_xs_1712_, lean_object* v_i_1713_, lean_object* v_x_1714_, lean_object* v_hi_1715_){
_start:
{
lean_object* v_e_1716_; lean_object* v_xs_x27_1717_; lean_object* v___x_1718_; 
v_e_1716_ = lean_array_fget(v_xs_1712_, v_i_1713_);
v_xs_x27_1717_ = lean_array_fset(v_xs_1712_, v_i_1713_, v_x_1714_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_e_1716_);
lean_ctor_set(v___x_1718_, 1, v_xs_x27_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_n_1720_, lean_object* v_xs_1721_, lean_object* v_i_1722_, lean_object* v_x_1723_, lean_object* v_hi_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Vector_swapAt(v_00_u03b1_1719_, v_n_1720_, v_xs_1721_, v_i_1722_, v_x_1723_, v_hi_1724_);
lean_dec(v_i_1722_);
lean_dec(v_n_1720_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1730_, lean_object* v_i_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = lean_array_get_size(v_xs_1730_);
v___x_1734_ = lean_nat_dec_lt(v_i_1731_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v_this_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
v_this_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1735_, 0, v_x_1732_);
lean_ctor_set(v_this_1735_, 1, v_xs_1730_);
v___x_1736_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1737_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1738_ = lean_unsigned_to_nat(463u);
v___x_1739_ = lean_unsigned_to_nat(4u);
v___x_1740_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1741_ = l_Nat_reprFast(v_i_1731_);
v___x_1742_ = lean_string_append(v___x_1740_, v___x_1741_);
lean_dec_ref(v___x_1741_);
v___x_1743_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
v___x_1745_ = l_mkPanicMessageWithDecl(v___x_1736_, v___x_1737_, v___x_1738_, v___x_1739_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = l_panic___redArg(v_this_1735_, v___x_1745_);
lean_dec_ref_known(v_this_1735_, 2);
v_fst_1747_ = lean_ctor_get(v___x_1746_, 0);
v_snd_1748_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1746_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_inc(v_fst_1747_);
lean_dec(v___x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_fst_1747_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_snd_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
else
{
lean_object* v_e_1756_; lean_object* v_xs_x27_1757_; lean_object* v___x_1758_; 
v_e_1756_ = lean_array_fget(v_xs_1730_, v_i_1731_);
v_xs_x27_1757_ = lean_array_fset(v_xs_1730_, v_i_1731_, v_x_1732_);
lean_dec(v_i_1731_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_e_1756_);
lean_ctor_set(v___x_1758_, 1, v_xs_x27_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1759_, lean_object* v_n_1760_, lean_object* v_xs_1761_, lean_object* v_i_1762_, lean_object* v_x_1763_){
_start:
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_array_get_size(v_xs_1761_);
v___x_1765_ = lean_nat_dec_lt(v_i_1762_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v_this_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_this_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1766_, 0, v_x_1763_);
lean_ctor_set(v_this_1766_, 1, v_xs_1761_);
v___x_1767_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1768_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1769_ = lean_unsigned_to_nat(463u);
v___x_1770_ = lean_unsigned_to_nat(4u);
v___x_1771_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1772_ = l_Nat_reprFast(v_i_1762_);
v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
v___x_1776_ = l_mkPanicMessageWithDecl(v___x_1767_, v___x_1768_, v___x_1769_, v___x_1770_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_panic___redArg(v_this_1766_, v___x_1776_);
lean_dec_ref_known(v_this_1766_, 2);
v_fst_1778_ = lean_ctor_get(v___x_1777_, 0);
v_snd_1779_ = lean_ctor_get(v___x_1777_, 1);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1777_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v___x_1777_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_fst_1778_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_snd_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
lean_object* v_e_1787_; lean_object* v_xs_x27_1788_; lean_object* v___x_1789_; 
v_e_1787_ = lean_array_fget(v_xs_1761_, v_i_1762_);
v_xs_x27_1788_ = lean_array_fset(v_xs_1761_, v_i_1762_, v_x_1763_);
lean_dec(v_i_1762_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_e_1787_);
lean_ctor_set(v___x_1789_, 1, v_xs_x27_1788_);
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_n_1791_, lean_object* v_xs_1792_, lean_object* v_i_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Vector_swapAt_x21(v_00_u03b1_1790_, v_n_1791_, v_xs_1792_, v_i_1793_, v_x_1794_);
lean_dec(v_n_1791_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Array_range(v_n_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1798_, lean_object* v_size_1799_, lean_object* v_step_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Array_range_x27(v_start_1798_, v_size_1799_, v_step_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1802_, lean_object* v_xs_1803_, lean_object* v_ys_1804_, lean_object* v_r_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Array_isEqvAux___redArg(v_xs_1803_, v_ys_1804_, v_r_1805_, v_n_1802_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1807_, lean_object* v_xs_1808_, lean_object* v_ys_1809_, lean_object* v_r_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Vector_isEqv___redArg(v_n_1807_, v_xs_1808_, v_ys_1809_, v_r_1810_);
lean_dec_ref(v_ys_1809_);
lean_dec_ref(v_xs_1808_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1813_, lean_object* v_n_1814_, lean_object* v_xs_1815_, lean_object* v_ys_1816_, lean_object* v_r_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Array_isEqvAux___redArg(v_xs_1815_, v_ys_1816_, v_r_1817_, v_n_1814_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_n_1820_, lean_object* v_xs_1821_, lean_object* v_ys_1822_, lean_object* v_r_1823_){
_start:
{
uint8_t v_res_1824_; lean_object* v_r_1825_; 
v_res_1824_ = l_Vector_isEqv(v_00_u03b1_1819_, v_n_1820_, v_xs_1821_, v_ys_1822_, v_r_1823_);
lean_dec_ref(v_ys_1822_);
lean_dec_ref(v_xs_1821_);
v_r_1825_ = lean_box(v_res_1824_);
return v_r_1825_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1826_, lean_object* v_x1_1827_, lean_object* v_x2_1828_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = lean_apply_2(v_inst_1826_, v_x1_1827_, v_x2_1828_);
v___x_1830_ = lean_unbox(v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1831_, lean_object* v_x1_1832_, lean_object* v_x2_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_Vector_instBEq___redArg___lam__0(v_inst_1831_, v_x1_1832_, v_x2_1833_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1836_, lean_object* v_n_1837_, lean_object* v_xs_1838_, lean_object* v_ys_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Array_isEqvAux___redArg(v_xs_1838_, v_ys_1839_, v___f_1836_, v_n_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1841_, lean_object* v_n_1842_, lean_object* v_xs_1843_, lean_object* v_ys_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Vector_instBEq___redArg___lam__1(v___f_1841_, v_n_1842_, v_xs_1843_, v_ys_1844_);
lean_dec_ref(v_ys_1844_);
lean_dec_ref(v_xs_1843_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1847_, lean_object* v_inst_1848_){
_start:
{
lean_object* v___f_1849_; lean_object* v___f_1850_; 
v___f_1849_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1849_, 0, v_inst_1848_);
v___f_1850_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1850_, 0, v___f_1849_);
lean_closure_set(v___f_1850_, 1, v_n_1847_);
return v___f_1850_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1851_, lean_object* v_n_1852_, lean_object* v_inst_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Vector_instBEq___redArg(v_n_1852_, v_inst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Array_reverse___redArg(v_xs_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1857_, lean_object* v_n_1858_, lean_object* v_xs_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Array_reverse___redArg(v_xs_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_n_1862_, lean_object* v_xs_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Vector_reverse(v_00_u03b1_1861_, v_n_1862_, v_xs_1863_);
lean_dec(v_n_1862_);
return v_res_1864_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1866_, lean_object* v_i_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Array_eraseIdx___redArg(v_xs_1866_, v_i_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1869_, lean_object* v_n_1870_, lean_object* v_xs_1871_, lean_object* v_i_1872_, lean_object* v_h_1873_){
_start:
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Array_eraseIdx___redArg(v_xs_1871_, v_i_1872_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1875_, lean_object* v_n_1876_, lean_object* v_xs_1877_, lean_object* v_i_1878_, lean_object* v_h_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Vector_eraseIdx(v_00_u03b1_1875_, v_n_1876_, v_xs_1877_, v_i_1878_, v_h_1879_);
lean_dec(v_n_1876_);
return v_res_1880_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1884_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1885_ = lean_unsigned_to_nat(4u);
v___x_1886_ = lean_unsigned_to_nat(430u);
v___x_1887_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1888_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1889_ = l_mkPanicMessageWithDecl(v___x_1888_, v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1890_, lean_object* v_xs_1891_, lean_object* v_i_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_lt(v_i_1892_, v_n_1890_);
if (v___x_1893_ == 0)
{
lean_object* v_this_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
lean_dec(v_i_1892_);
v_this_1894_ = lean_array_pop(v_xs_1891_);
v___x_1895_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1896_ = l_panic___redArg(v_this_1894_, v___x_1895_);
lean_dec_ref(v_this_1894_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Array_eraseIdx___redArg(v_xs_1891_, v_i_1892_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1898_, lean_object* v_xs_1899_, lean_object* v_i_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Vector_eraseIdx_x21___redArg(v_n_1898_, v_xs_1899_, v_i_1900_);
lean_dec(v_n_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1902_, lean_object* v_n_1903_, lean_object* v_xs_1904_, lean_object* v_i_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_nat_dec_lt(v_i_1905_, v_n_1903_);
if (v___x_1906_ == 0)
{
lean_object* v_this_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_i_1905_);
v_this_1907_ = lean_array_pop(v_xs_1904_);
v___x_1908_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1909_ = l_panic___redArg(v_this_1907_, v___x_1908_);
lean_dec_ref(v_this_1907_);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Array_eraseIdx___redArg(v_xs_1904_, v_i_1905_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1911_, lean_object* v_n_1912_, lean_object* v_xs_1913_, lean_object* v_i_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Vector_eraseIdx_x21(v_00_u03b1_1911_, v_n_1912_, v_xs_1913_, v_i_1914_);
lean_dec(v_n_1912_);
return v_res_1915_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1917_, lean_object* v_i_1918_, lean_object* v_x_1919_){
_start:
{
lean_object* v_j_1920_; lean_object* v_as_1921_; lean_object* v___x_1922_; 
v_j_1920_ = lean_array_get_size(v_xs_1917_);
v_as_1921_ = lean_array_push(v_xs_1917_, v_x_1919_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1918_, v_as_1921_, v_j_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1923_, lean_object* v_i_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Vector_insertIdx___redArg(v_xs_1923_, v_i_1924_, v_x_1925_);
lean_dec(v_i_1924_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1927_, lean_object* v_n_1928_, lean_object* v_xs_1929_, lean_object* v_i_1930_, lean_object* v_x_1931_, lean_object* v_h_1932_){
_start:
{
lean_object* v_j_1933_; lean_object* v_as_1934_; lean_object* v___x_1935_; 
v_j_1933_ = lean_array_get_size(v_xs_1929_);
v_as_1934_ = lean_array_push(v_xs_1929_, v_x_1931_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1930_, v_as_1934_, v_j_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1936_, lean_object* v_n_1937_, lean_object* v_xs_1938_, lean_object* v_i_1939_, lean_object* v_x_1940_, lean_object* v_h_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Vector_insertIdx(v_00_u03b1_1936_, v_n_1937_, v_xs_1938_, v_i_1939_, v_x_1940_, v_h_1941_);
lean_dec(v_i_1939_);
lean_dec(v_n_1937_);
return v_res_1942_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1944_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1945_ = lean_unsigned_to_nat(4u);
v___x_1946_ = lean_unsigned_to_nat(443u);
v___x_1947_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1948_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1949_ = l_mkPanicMessageWithDecl(v___x_1948_, v___x_1947_, v___x_1946_, v___x_1945_, v___x_1944_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1950_, lean_object* v_xs_1951_, lean_object* v_i_1952_, lean_object* v_x_1953_){
_start:
{
uint8_t v___x_1954_; 
v___x_1954_ = lean_nat_dec_le(v_i_1952_, v_n_1950_);
if (v___x_1954_ == 0)
{
lean_object* v_this_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_this_1955_ = lean_array_push(v_xs_1951_, v_x_1953_);
v___x_1956_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1957_ = l_panic___redArg(v_this_1955_, v___x_1956_);
lean_dec_ref(v_this_1955_);
return v___x_1957_;
}
else
{
lean_object* v_j_1958_; lean_object* v_as_1959_; lean_object* v___x_1960_; 
v_j_1958_ = lean_array_get_size(v_xs_1951_);
v_as_1959_ = lean_array_push(v_xs_1951_, v_x_1953_);
v___x_1960_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1952_, v_as_1959_, v_j_1958_);
return v___x_1960_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1961_, lean_object* v_xs_1962_, lean_object* v_i_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Vector_insertIdx_x21___redArg(v_n_1961_, v_xs_1962_, v_i_1963_, v_x_1964_);
lean_dec(v_i_1963_);
lean_dec(v_n_1961_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1966_, lean_object* v_n_1967_, lean_object* v_xs_1968_, lean_object* v_i_1969_, lean_object* v_x_1970_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_nat_dec_le(v_i_1969_, v_n_1967_);
if (v___x_1971_ == 0)
{
lean_object* v_this_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_this_1972_ = lean_array_push(v_xs_1968_, v_x_1970_);
v___x_1973_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1974_ = l_panic___redArg(v_this_1972_, v___x_1973_);
lean_dec_ref(v_this_1972_);
return v___x_1974_;
}
else
{
lean_object* v_j_1975_; lean_object* v_as_1976_; lean_object* v___x_1977_; 
v_j_1975_ = lean_array_get_size(v_xs_1968_);
v_as_1976_ = lean_array_push(v_xs_1968_, v_x_1970_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1969_, v_as_1976_, v_j_1975_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_n_1979_, lean_object* v_xs_1980_, lean_object* v_i_1981_, lean_object* v_x_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Vector_insertIdx_x21(v_00_u03b1_1978_, v_n_1979_, v_xs_1980_, v_i_1981_, v_x_1982_);
lean_dec(v_i_1981_);
lean_dec(v_n_1979_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_1984_, lean_object* v_xs_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = l_Array_extract___redArg(v_xs_1985_, v___x_1986_, v_n_1984_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_1988_, lean_object* v_xs_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Vector_tail___redArg(v_n_1988_, v_xs_1989_);
lean_dec_ref(v_xs_1989_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_1991_, lean_object* v_n_1992_, lean_object* v_xs_1993_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = l_Array_extract___redArg(v_xs_1993_, v___x_1994_, v_n_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_1996_, lean_object* v_n_1997_, lean_object* v_xs_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Vector_tail(v_00_u03b1_1996_, v_n_1997_, v_xs_1998_);
lean_dec_ref(v_xs_1998_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2000_, lean_object* v_xs_2001_, lean_object* v_x_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Array_finIdxOf_x3f___redArg(v_inst_2000_, v_xs_2001_, v_x_2002_);
if (lean_obj_tag(v___x_2003_) == 0)
{
return v___x_2003_;
}
else
{
lean_object* v_val_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
v_val_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_val_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2012_, lean_object* v_xs_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2012_, v_xs_2013_, v_x_2014_);
lean_dec_ref(v_xs_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2016_, lean_object* v_n_2017_, lean_object* v_inst_2018_, lean_object* v_xs_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Array_finIdxOf_x3f___redArg(v_inst_2018_, v_xs_2019_, v_x_2020_);
if (lean_obj_tag(v___x_2021_) == 0)
{
return v___x_2021_;
}
else
{
lean_object* v_val_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_val_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_val_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_val_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2030_, lean_object* v_n_2031_, lean_object* v_inst_2032_, lean_object* v_xs_2033_, lean_object* v_x_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2030_, v_n_2031_, v_inst_2032_, v_xs_2033_, v_x_2034_);
lean_dec_ref(v_xs_2033_);
lean_dec(v_n_2031_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2036_, lean_object* v_xs_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2036_, v_xs_2037_, v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
return v___x_2039_;
}
else
{
lean_object* v_val_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_val_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_val_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_val_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2048_, lean_object* v_xs_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Vector_findFinIdx_x3f___redArg(v_p_2048_, v_xs_2049_);
lean_dec_ref(v_xs_2049_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2051_, lean_object* v_n_2052_, lean_object* v_p_2053_, lean_object* v_xs_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2053_, v_xs_2054_, v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_val_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2065_, lean_object* v_n_2066_, lean_object* v_p_2067_, lean_object* v_xs_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2065_, v_n_2066_, v_p_2067_, v_xs_2068_);
lean_dec_ref(v_xs_2068_);
lean_dec(v_n_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2070_, lean_object* v_____s_2071_){
_start:
{
lean_object* v_fst_2072_; 
v_fst_2072_ = lean_ctor_get(v_____s_2071_, 0);
lean_inc(v_fst_2072_);
lean_dec_ref(v_____s_2071_);
if (lean_obj_tag(v_fst_2072_) == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_apply_2(v_toPure_2070_, lean_box(0), v___x_2073_);
return v___x_2074_;
}
else
{
lean_object* v_val_2075_; lean_object* v___x_2076_; 
v_val_2075_ = lean_ctor_get(v_fst_2072_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v_fst_2072_, 1);
v___x_2076_ = lean_apply_2(v_toPure_2070_, lean_box(0), v_val_2075_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2077_, lean_object* v_toPure_2078_, lean_object* v_a_2079_, lean_object* v___x_2080_, uint8_t v_____do__lift_2081_){
_start:
{
if (v_____do__lift_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v_a_2079_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2077_);
v___x_2083_ = lean_apply_2(v_toPure_2078_, lean_box(0), v___x_2082_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec_ref(v___x_2077_);
v___x_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_a_2079_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
lean_ctor_set(v___x_2086_, 1, v___x_2080_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
v___x_2088_ = lean_apply_2(v_toPure_2078_, lean_box(0), v___x_2087_);
return v___x_2088_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2089_, lean_object* v_toPure_2090_, lean_object* v_a_2091_, lean_object* v___x_2092_, lean_object* v_____do__lift_2093_){
_start:
{
uint8_t v_____do__lift_124__boxed_2094_; lean_object* v_res_2095_; 
v_____do__lift_124__boxed_2094_ = lean_unbox(v_____do__lift_2093_);
v_res_2095_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2089_, v_toPure_2090_, v_a_2091_, v___x_2092_, v_____do__lift_124__boxed_2094_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2096_, lean_object* v_toPure_2097_, lean_object* v___x_2098_, lean_object* v_f_2099_, lean_object* v_toBind_2100_, lean_object* v_a_2101_, lean_object* v_x_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___f_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_inc(v_a_2101_);
v___f_2104_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2104_, 0, v___x_2096_);
lean_closure_set(v___f_2104_, 1, v_toPure_2097_);
lean_closure_set(v___f_2104_, 2, v_a_2101_);
lean_closure_set(v___f_2104_, 3, v___x_2098_);
v___x_2105_ = lean_apply_1(v_f_2099_, v_a_2101_);
v___x_2106_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v___x_2105_, v___f_2104_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2107_, lean_object* v_toPure_2108_, lean_object* v___x_2109_, lean_object* v_f_2110_, lean_object* v_toBind_2111_, lean_object* v_a_2112_, lean_object* v_x_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2107_, v_toPure_2108_, v___x_2109_, v_f_2110_, v_toBind_2111_, v_a_2112_, v_x_2113_, v___y_2114_);
lean_dec_ref(v___y_2114_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2119_, lean_object* v_f_2120_, lean_object* v_as_2121_){
_start:
{
lean_object* v_toApplicative_2122_; lean_object* v_toBind_2123_; lean_object* v_toPure_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_toApplicative_2122_ = lean_ctor_get(v_inst_2119_, 0);
v_toBind_2123_ = lean_ctor_get(v_inst_2119_, 1);
lean_inc_n(v_toBind_2123_, 2);
v_toPure_2124_ = lean_ctor_get(v_toApplicative_2122_, 1);
v___x_2125_ = lean_box(0);
v___x_2126_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2124_, 2);
v___f_2127_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2127_, 0, v_toPure_2124_);
v___f_2128_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2128_, 0, v___x_2126_);
lean_closure_set(v___f_2128_, 1, v_toPure_2124_);
lean_closure_set(v___f_2128_, 2, v___x_2125_);
lean_closure_set(v___f_2128_, 3, v_f_2120_);
lean_closure_set(v___f_2128_, 4, v_toBind_2123_);
v_sz_2129_ = lean_array_size(v_as_2121_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2119_, v_as_2121_, v___f_2128_, v_sz_2129_, v___x_2130_, v___x_2126_);
v___x_2132_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v___x_2131_, v___f_2127_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2133_, lean_object* v_00_u03b1_2134_, lean_object* v_m_2135_, lean_object* v_inst_2136_, lean_object* v_f_2137_, lean_object* v_as_2138_){
_start:
{
lean_object* v_toApplicative_2139_; lean_object* v_toBind_2140_; lean_object* v_toPure_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; lean_object* v___f_2145_; size_t v_sz_2146_; size_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_toApplicative_2139_ = lean_ctor_get(v_inst_2136_, 0);
v_toBind_2140_ = lean_ctor_get(v_inst_2136_, 1);
lean_inc_n(v_toBind_2140_, 2);
v_toPure_2141_ = lean_ctor_get(v_toApplicative_2139_, 1);
v___x_2142_ = lean_box(0);
v___x_2143_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2141_, 2);
v___f_2144_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2144_, 0, v_toPure_2141_);
v___f_2145_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2145_, 0, v___x_2143_);
lean_closure_set(v___f_2145_, 1, v_toPure_2141_);
lean_closure_set(v___f_2145_, 2, v___x_2142_);
lean_closure_set(v___f_2145_, 3, v_f_2137_);
lean_closure_set(v___f_2145_, 4, v_toBind_2140_);
v_sz_2146_ = lean_array_size(v_as_2138_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2136_, v_as_2138_, v___f_2145_, v_sz_2146_, v___x_2147_, v___x_2143_);
v___x_2149_ = lean_apply_4(v_toBind_2140_, lean_box(0), lean_box(0), v___x_2148_, v___f_2144_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2150_, lean_object* v_00_u03b1_2151_, lean_object* v_m_2152_, lean_object* v_inst_2153_, lean_object* v_f_2154_, lean_object* v_as_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Vector_findM_x3f(v_n_2150_, v_00_u03b1_2151_, v_m_2152_, v_inst_2153_, v_f_2154_, v_as_2155_);
lean_dec(v_n_2150_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2157_, lean_object* v_toPure_2158_, lean_object* v___x_2159_, lean_object* v_____do__lift_2160_){
_start:
{
if (lean_obj_tag(v_____do__lift_2160_) == 1)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v___x_2159_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_____do__lift_2160_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2157_);
v___x_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
v___x_2164_ = lean_apply_2(v_toPure_2158_, lean_box(0), v___x_2163_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_____do__lift_2160_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2159_);
v___x_2166_ = lean_apply_2(v_toPure_2158_, lean_box(0), v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2167_, lean_object* v_toBind_2168_, lean_object* v___f_2169_, lean_object* v_a_2170_, lean_object* v_x_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_apply_1(v_f_2167_, v_a_2170_);
v___x_2174_ = lean_apply_4(v_toBind_2168_, lean_box(0), lean_box(0), v___x_2173_, v___f_2169_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2175_, lean_object* v_toBind_2176_, lean_object* v___f_2177_, lean_object* v_a_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2175_, v_toBind_2176_, v___f_2177_, v_a_2178_, v_x_2179_, v___y_2180_);
lean_dec_ref(v___y_2180_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2182_, lean_object* v_f_2183_, lean_object* v_as_2184_){
_start:
{
lean_object* v_toApplicative_2185_; lean_object* v_toBind_2186_; lean_object* v_toPure_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; size_t v_sz_2193_; size_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_toApplicative_2185_ = lean_ctor_get(v_inst_2182_, 0);
v_toBind_2186_ = lean_ctor_get(v_inst_2182_, 1);
lean_inc_n(v_toBind_2186_, 2);
v_toPure_2187_ = lean_ctor_get(v_toApplicative_2185_, 1);
v___x_2188_ = lean_box(0);
v___x_2189_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2187_, 2);
v___f_2190_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2190_, 0, v_toPure_2187_);
v___f_2191_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2191_, 0, v___x_2188_);
lean_closure_set(v___f_2191_, 1, v_toPure_2187_);
lean_closure_set(v___f_2191_, 2, v___x_2189_);
v___f_2192_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2192_, 0, v_f_2183_);
lean_closure_set(v___f_2192_, 1, v_toBind_2186_);
lean_closure_set(v___f_2192_, 2, v___f_2191_);
v_sz_2193_ = lean_array_size(v_as_2184_);
v___x_2194_ = ((size_t)0ULL);
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2182_, v_as_2184_, v___f_2192_, v_sz_2193_, v___x_2194_, v___x_2189_);
v___x_2196_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2195_, v___f_2190_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2197_, lean_object* v_00_u03b1_2198_, lean_object* v_00_u03b2_2199_, lean_object* v_n_2200_, lean_object* v_inst_2201_, lean_object* v_f_2202_, lean_object* v_as_2203_){
_start:
{
lean_object* v_toApplicative_2204_; lean_object* v_toBind_2205_; lean_object* v_toPure_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___f_2211_; size_t v_sz_2212_; size_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_toApplicative_2204_ = lean_ctor_get(v_inst_2201_, 0);
v_toBind_2205_ = lean_ctor_get(v_inst_2201_, 1);
lean_inc_n(v_toBind_2205_, 2);
v_toPure_2206_ = lean_ctor_get(v_toApplicative_2204_, 1);
v___x_2207_ = lean_box(0);
v___x_2208_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2206_, 2);
v___f_2209_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2209_, 0, v_toPure_2206_);
v___f_2210_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2210_, 0, v___x_2207_);
lean_closure_set(v___f_2210_, 1, v_toPure_2206_);
lean_closure_set(v___f_2210_, 2, v___x_2208_);
v___f_2211_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2211_, 0, v_f_2202_);
lean_closure_set(v___f_2211_, 1, v_toBind_2205_);
lean_closure_set(v___f_2211_, 2, v___f_2210_);
v_sz_2212_ = lean_array_size(v_as_2203_);
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2201_, v_as_2203_, v___f_2211_, v_sz_2212_, v___x_2213_, v___x_2208_);
v___x_2215_ = lean_apply_4(v_toBind_2205_, lean_box(0), lean_box(0), v___x_2214_, v___f_2209_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2216_, lean_object* v_00_u03b1_2217_, lean_object* v_00_u03b2_2218_, lean_object* v_n_2219_, lean_object* v_inst_2220_, lean_object* v_f_2221_, lean_object* v_as_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Vector_findSomeM_x3f(v_m_2216_, v_00_u03b1_2217_, v_00_u03b2_2218_, v_n_2219_, v_inst_2220_, v_f_2221_, v_as_2222_);
lean_dec(v_n_2219_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2224_, lean_object* v_a_2225_, uint8_t v_____do__lift_2226_){
_start:
{
if (v_____do__lift_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
lean_dec(v_a_2225_);
v___x_2227_ = lean_box(0);
v___x_2228_ = lean_apply_2(v_toPure_2224_, lean_box(0), v___x_2227_);
return v___x_2228_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_a_2225_);
v___x_2230_ = lean_apply_2(v_toPure_2224_, lean_box(0), v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2231_, lean_object* v_a_2232_, lean_object* v_____do__lift_2233_){
_start:
{
uint8_t v_____do__lift_50__boxed_2234_; lean_object* v_res_2235_; 
v_____do__lift_50__boxed_2234_ = lean_unbox(v_____do__lift_2233_);
v_res_2235_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2231_, v_a_2232_, v_____do__lift_50__boxed_2234_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2236_, lean_object* v_f_2237_, lean_object* v_toBind_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_inc(v_a_2239_);
v___f_2240_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2240_, 0, v_toPure_2236_);
lean_closure_set(v___f_2240_, 1, v_a_2239_);
v___x_2241_ = lean_apply_1(v_f_2237_, v_a_2239_);
v___x_2242_ = lean_apply_4(v_toBind_2238_, lean_box(0), lean_box(0), v___x_2241_, v___f_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2243_, lean_object* v_f_2244_, lean_object* v_as_2245_){
_start:
{
lean_object* v_toApplicative_2246_; lean_object* v_toBind_2247_; lean_object* v_toPure_2248_; lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_toApplicative_2246_ = lean_ctor_get(v_inst_2243_, 0);
v_toBind_2247_ = lean_ctor_get(v_inst_2243_, 1);
v_toPure_2248_ = lean_ctor_get(v_toApplicative_2246_, 1);
lean_inc(v_toBind_2247_);
lean_inc(v_toPure_2248_);
v___f_2249_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2249_, 0, v_toPure_2248_);
lean_closure_set(v___f_2249_, 1, v_f_2244_);
lean_closure_set(v___f_2249_, 2, v_toBind_2247_);
v___x_2250_ = lean_array_get_size(v_as_2245_);
v___x_2251_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2243_, v___f_2249_, v_as_2245_, v___x_2250_, lean_box(0));
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2252_, lean_object* v_00_u03b1_2253_, lean_object* v_m_2254_, lean_object* v_inst_2255_, lean_object* v_f_2256_, lean_object* v_as_2257_){
_start:
{
lean_object* v_toApplicative_2258_; lean_object* v_toBind_2259_; lean_object* v_toPure_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_toApplicative_2258_ = lean_ctor_get(v_inst_2255_, 0);
v_toBind_2259_ = lean_ctor_get(v_inst_2255_, 1);
v_toPure_2260_ = lean_ctor_get(v_toApplicative_2258_, 1);
lean_inc(v_toBind_2259_);
lean_inc(v_toPure_2260_);
v___f_2261_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2261_, 0, v_toPure_2260_);
lean_closure_set(v___f_2261_, 1, v_f_2256_);
lean_closure_set(v___f_2261_, 2, v_toBind_2259_);
v___x_2262_ = lean_array_get_size(v_as_2257_);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2255_, v___f_2261_, v_as_2257_, v___x_2262_, lean_box(0));
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2264_, lean_object* v_00_u03b1_2265_, lean_object* v_m_2266_, lean_object* v_inst_2267_, lean_object* v_f_2268_, lean_object* v_as_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Vector_findRevM_x3f(v_n_2264_, v_00_u03b1_2265_, v_m_2266_, v_inst_2267_, v_f_2268_, v_as_2269_);
lean_dec(v_n_2264_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2271_, lean_object* v_f_2272_, lean_object* v_as_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = lean_array_get_size(v_as_2273_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2271_, v_f_2272_, v_as_2273_, v___x_2274_, lean_box(0));
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2276_, lean_object* v_00_u03b1_2277_, lean_object* v_00_u03b2_2278_, lean_object* v_n_2279_, lean_object* v_inst_2280_, lean_object* v_f_2281_, lean_object* v_as_2282_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_array_get_size(v_as_2282_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2280_, v_f_2281_, v_as_2282_, v___x_2283_, lean_box(0));
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2285_, lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_n_2288_, lean_object* v_inst_2289_, lean_object* v_f_2290_, lean_object* v_as_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Vector_findSomeRevM_x3f(v_m_2285_, v_00_u03b1_2286_, v_00_u03b2_2287_, v_n_2288_, v_inst_2289_, v_f_2290_, v_as_2291_);
lean_dec(v_n_2288_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2293_, lean_object* v___x_2294_, lean_object* v___x_2295_, lean_object* v_a_2296_, lean_object* v_x_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
lean_inc(v_a_2296_);
v___x_2299_ = lean_apply_1(v_f_2293_, v_a_2296_);
v___x_2300_ = lean_unbox(v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; 
lean_dec(v_a_2296_);
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2294_);
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec_ref(v___x_2294_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2296_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2295_);
v___x_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2306_, lean_object* v___x_2307_, lean_object* v___x_2308_, lean_object* v_a_2309_, lean_object* v_x_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Vector_find_x3f___redArg___lam__0(v_f_2306_, v___x_2307_, v___x_2308_, v_a_2309_, v_x_2310_, v___y_2311_);
lean_dec_ref(v___y_2311_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2313_, lean_object* v_as_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; size_t v_sz_2320_; size_t v___x_2321_; lean_object* v___x_2322_; lean_object* v_fst_2323_; 
v___x_2315_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_box(0);
v___x_2318_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2319_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2319_, 0, v_f_2313_);
lean_closure_set(v___f_2319_, 1, v___x_2318_);
lean_closure_set(v___f_2319_, 2, v___x_2317_);
v_sz_2320_ = lean_array_size(v_as_2314_);
v___x_2321_ = ((size_t)0ULL);
v___x_2322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2315_, v_as_2314_, v___f_2319_, v_sz_2320_, v___x_2321_, v___x_2318_);
v_fst_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_fst_2323_);
lean_dec(v___x_2322_);
if (lean_obj_tag(v_fst_2323_) == 0)
{
return v___x_2316_;
}
else
{
lean_object* v_val_2324_; 
v_val_2324_ = lean_ctor_get(v_fst_2323_, 0);
lean_inc(v_val_2324_);
lean_dec_ref_known(v_fst_2323_, 1);
return v_val_2324_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2325_, lean_object* v_00_u03b1_2326_, lean_object* v_f_2327_, lean_object* v_as_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___f_2333_; size_t v_sz_2334_; size_t v___x_2335_; lean_object* v___x_2336_; lean_object* v_fst_2337_; 
v___x_2329_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_box(0);
v___x_2332_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2333_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2333_, 0, v_f_2327_);
lean_closure_set(v___f_2333_, 1, v___x_2332_);
lean_closure_set(v___f_2333_, 2, v___x_2331_);
v_sz_2334_ = lean_array_size(v_as_2328_);
v___x_2335_ = ((size_t)0ULL);
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2329_, v_as_2328_, v___f_2333_, v_sz_2334_, v___x_2335_, v___x_2332_);
v_fst_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_fst_2337_);
lean_dec(v___x_2336_);
if (lean_obj_tag(v_fst_2337_) == 0)
{
return v___x_2330_;
}
else
{
lean_object* v_val_2338_; 
v_val_2338_ = lean_ctor_get(v_fst_2337_, 0);
lean_inc(v_val_2338_);
lean_dec_ref_known(v_fst_2337_, 1);
return v_val_2338_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2339_, lean_object* v_00_u03b1_2340_, lean_object* v_f_2341_, lean_object* v_as_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Vector_find_x3f(v_n_2339_, v_00_u03b1_2340_, v_f_2341_, v_as_2342_);
lean_dec(v_n_2339_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2346_; uint8_t v___x_2347_; 
lean_inc(v_a_2345_);
v___x_2346_ = lean_apply_1(v_f_2344_, v_a_2345_);
v___x_2347_ = lean_unbox(v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_a_2345_);
v___x_2348_ = lean_box(0);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2349_, 0, v_a_2345_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2350_, lean_object* v_as_2351_){
_start:
{
lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___f_2352_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2352_, 0, v_f_2350_);
v___x_2353_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2354_ = lean_array_get_size(v_as_2351_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2353_, v___f_2352_, v_as_2351_, v___x_2354_, lean_box(0));
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2356_, lean_object* v_00_u03b1_2357_, lean_object* v_f_2358_, lean_object* v_as_2359_){
_start:
{
lean_object* v___f_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___f_2360_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2360_, 0, v_f_2358_);
v___x_2361_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2362_ = lean_array_get_size(v_as_2359_);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2361_, v___f_2360_, v_as_2359_, v___x_2362_, lean_box(0));
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2364_, lean_object* v_00_u03b1_2365_, lean_object* v_f_2366_, lean_object* v_as_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Vector_findRev_x3f(v_n_2364_, v_00_u03b1_2365_, v_f_2366_, v_as_2367_);
lean_dec(v_n_2364_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v_a_2372_, lean_object* v_x_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = lean_apply_1(v_f_2369_, v_a_2372_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_dec_ref(v___x_2371_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2370_);
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v___x_2379_; 
lean_dec(v___x_2375_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2371_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v_a_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2380_, v___x_2381_, v___x_2382_, v_a_2383_, v_x_2384_, v___y_2385_);
lean_dec_ref(v___y_2385_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2387_, lean_object* v_as_2388_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; lean_object* v_fst_2397_; 
v___x_2389_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_box(0);
v___x_2392_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2393_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2393_, 0, v_f_2387_);
lean_closure_set(v___f_2393_, 1, v___x_2391_);
lean_closure_set(v___f_2393_, 2, v___x_2392_);
v_sz_2394_ = lean_array_size(v_as_2388_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2389_, v_as_2388_, v___f_2393_, v_sz_2394_, v___x_2395_, v___x_2392_);
v_fst_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_fst_2397_);
lean_dec(v___x_2396_);
if (lean_obj_tag(v_fst_2397_) == 0)
{
return v___x_2390_;
}
else
{
lean_object* v_val_2398_; 
v_val_2398_ = lean_ctor_get(v_fst_2397_, 0);
lean_inc(v_val_2398_);
lean_dec_ref_known(v_fst_2397_, 1);
return v_val_2398_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2399_, lean_object* v_00_u03b2_2400_, lean_object* v_n_2401_, lean_object* v_f_2402_, lean_object* v_as_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___f_2408_; size_t v_sz_2409_; size_t v___x_2410_; lean_object* v___x_2411_; lean_object* v_fst_2412_; 
v___x_2404_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_box(0);
v___x_2407_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2408_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2408_, 0, v_f_2402_);
lean_closure_set(v___f_2408_, 1, v___x_2406_);
lean_closure_set(v___f_2408_, 2, v___x_2407_);
v_sz_2409_ = lean_array_size(v_as_2403_);
v___x_2410_ = ((size_t)0ULL);
v___x_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2404_, v_as_2403_, v___f_2408_, v_sz_2409_, v___x_2410_, v___x_2407_);
v_fst_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_fst_2412_);
lean_dec(v___x_2411_);
if (lean_obj_tag(v_fst_2412_) == 0)
{
return v___x_2405_;
}
else
{
lean_object* v_val_2413_; 
v_val_2413_ = lean_ctor_get(v_fst_2412_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v_fst_2412_, 1);
return v_val_2413_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_n_2416_, lean_object* v_f_2417_, lean_object* v_as_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Vector_findSome_x3f(v_00_u03b1_2414_, v_00_u03b2_2415_, v_n_2416_, v_f_2417_, v_as_2418_);
lean_dec(v_n_2416_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2420_, lean_object* v_x_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_apply_1(v_f_2420_, v_x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2423_, lean_object* v_as_2424_){
_start:
{
lean_object* v___f_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___f_2425_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2425_, 0, v_f_2423_);
v___x_2426_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2427_ = lean_array_get_size(v_as_2424_);
v___x_2428_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2426_, v___f_2425_, v_as_2424_, v___x_2427_, lean_box(0));
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2429_, lean_object* v_00_u03b2_2430_, lean_object* v_n_2431_, lean_object* v_f_2432_, lean_object* v_as_2433_){
_start:
{
lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___f_2434_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2434_, 0, v_f_2432_);
v___x_2435_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2436_ = lean_array_get_size(v_as_2433_);
v___x_2437_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2435_, v___f_2434_, v_as_2433_, v___x_2436_, lean_box(0));
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2438_, lean_object* v_00_u03b2_2439_, lean_object* v_n_2440_, lean_object* v_f_2441_, lean_object* v_as_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2438_, v_00_u03b2_2439_, v_n_2440_, v_f_2441_, v_as_2442_);
lean_dec(v_n_2440_);
return v_res_2443_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2444_, lean_object* v_xs_2445_, lean_object* v_ys_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Array_isPrefixOf___redArg(v_inst_2444_, v_xs_2445_, v_ys_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2448_, lean_object* v_xs_2449_, lean_object* v_ys_2450_){
_start:
{
uint8_t v_res_2451_; lean_object* v_r_2452_; 
v_res_2451_ = l_Vector_isPrefixOf___redArg(v_inst_2448_, v_xs_2449_, v_ys_2450_);
lean_dec_ref(v_ys_2450_);
lean_dec_ref(v_xs_2449_);
v_r_2452_ = lean_box(v_res_2451_);
return v_r_2452_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2453_, lean_object* v_m_2454_, lean_object* v_n_2455_, lean_object* v_inst_2456_, lean_object* v_xs_2457_, lean_object* v_ys_2458_){
_start:
{
uint8_t v___x_2459_; 
v___x_2459_ = l_Array_isPrefixOf___redArg(v_inst_2456_, v_xs_2457_, v_ys_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2460_, lean_object* v_m_2461_, lean_object* v_n_2462_, lean_object* v_inst_2463_, lean_object* v_xs_2464_, lean_object* v_ys_2465_){
_start:
{
uint8_t v_res_2466_; lean_object* v_r_2467_; 
v_res_2466_ = l_Vector_isPrefixOf(v_00_u03b1_2460_, v_m_2461_, v_n_2462_, v_inst_2463_, v_xs_2464_, v_ys_2465_);
lean_dec_ref(v_ys_2465_);
lean_dec_ref(v_xs_2464_);
lean_dec(v_n_2462_);
lean_dec(v_m_2461_);
v_r_2467_ = lean_box(v_res_2466_);
return v_r_2467_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2468_, lean_object* v_p_2469_, lean_object* v_xs_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toPure_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2468_, 0);
v_toPure_2472_ = lean_ctor_get(v_toApplicative_2471_, 1);
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = lean_array_get_size(v_xs_2470_);
v___x_2475_ = lean_nat_dec_lt(v___x_2473_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_inc(v_toPure_2472_);
lean_dec_ref(v_xs_2470_);
lean_dec(v_p_2469_);
lean_dec_ref(v_inst_2468_);
v___x_2476_ = lean_box(v___x_2475_);
v___x_2477_ = lean_apply_2(v_toPure_2472_, lean_box(0), v___x_2476_);
return v___x_2477_;
}
else
{
if (v___x_2475_ == 0)
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_inc(v_toPure_2472_);
lean_dec_ref(v_xs_2470_);
lean_dec(v_p_2469_);
lean_dec_ref(v_inst_2468_);
v___x_2478_ = lean_box(v___x_2475_);
v___x_2479_ = lean_apply_2(v_toPure_2472_, lean_box(0), v___x_2478_);
return v___x_2479_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((size_t)0ULL);
v___x_2481_ = lean_usize_of_nat(v___x_2474_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2468_, v_p_2469_, v_xs_2470_, v___x_2480_, v___x_2481_);
return v___x_2482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2483_, lean_object* v_00_u03b1_2484_, lean_object* v_n_2485_, lean_object* v_inst_2486_, lean_object* v_p_2487_, lean_object* v_xs_2488_){
_start:
{
lean_object* v_toApplicative_2489_; lean_object* v_toPure_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v_toApplicative_2489_ = lean_ctor_get(v_inst_2486_, 0);
v_toPure_2490_ = lean_ctor_get(v_toApplicative_2489_, 1);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_array_get_size(v_xs_2488_);
v___x_2493_ = lean_nat_dec_lt(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_inc(v_toPure_2490_);
lean_dec_ref(v_xs_2488_);
lean_dec(v_p_2487_);
lean_dec_ref(v_inst_2486_);
v___x_2494_ = lean_box(v___x_2493_);
v___x_2495_ = lean_apply_2(v_toPure_2490_, lean_box(0), v___x_2494_);
return v___x_2495_;
}
else
{
if (v___x_2493_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_inc(v_toPure_2490_);
lean_dec_ref(v_xs_2488_);
lean_dec(v_p_2487_);
lean_dec_ref(v_inst_2486_);
v___x_2496_ = lean_box(v___x_2493_);
v___x_2497_ = lean_apply_2(v_toPure_2490_, lean_box(0), v___x_2496_);
return v___x_2497_;
}
else
{
size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((size_t)0ULL);
v___x_2499_ = lean_usize_of_nat(v___x_2492_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2486_, v_p_2487_, v_xs_2488_, v___x_2498_, v___x_2499_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2501_, lean_object* v_00_u03b1_2502_, lean_object* v_n_2503_, lean_object* v_inst_2504_, lean_object* v_p_2505_, lean_object* v_xs_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Vector_anyM(v_m_2501_, v_00_u03b1_2502_, v_n_2503_, v_inst_2504_, v_p_2505_, v_xs_2506_);
lean_dec(v_n_2503_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2508_, uint8_t v_____do__lift_2509_){
_start:
{
if (v_____do__lift_2509_ == 0)
{
uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = 1;
v___x_2511_ = lean_box(v___x_2510_);
v___x_2512_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2511_);
return v___x_2512_;
}
else
{
uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = 0;
v___x_2514_ = lean_box(v___x_2513_);
v___x_2515_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2514_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2516_, lean_object* v_____do__lift_2517_){
_start:
{
uint8_t v_____do__lift_112__boxed_2518_; lean_object* v_res_2519_; 
v_____do__lift_112__boxed_2518_ = lean_unbox(v_____do__lift_2517_);
v_res_2519_ = l_Vector_allM___redArg___lam__0(v_toPure_2516_, v_____do__lift_112__boxed_2518_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2520_, uint8_t v___x_2521_, uint8_t v_____do__lift_2522_){
_start:
{
if (v_____do__lift_2522_ == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_box(v___x_2521_);
v___x_2524_ = lean_apply_2(v_toPure_2520_, lean_box(0), v___x_2523_);
return v___x_2524_;
}
else
{
uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = 0;
v___x_2526_ = lean_box(v___x_2525_);
v___x_2527_ = lean_apply_2(v_toPure_2520_, lean_box(0), v___x_2526_);
return v___x_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2528_, lean_object* v___x_2529_, lean_object* v_____do__lift_2530_){
_start:
{
uint8_t v___x_127__boxed_2531_; uint8_t v_____do__lift_128__boxed_2532_; lean_object* v_res_2533_; 
v___x_127__boxed_2531_ = lean_unbox(v___x_2529_);
v_____do__lift_128__boxed_2532_ = lean_unbox(v_____do__lift_2530_);
v_res_2533_ = l_Vector_allM___redArg___lam__1(v_toPure_2528_, v___x_127__boxed_2531_, v_____do__lift_128__boxed_2532_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2534_, lean_object* v_toBind_2535_, lean_object* v___f_2536_, lean_object* v_v_2537_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_apply_1(v_p_2534_, v_v_2537_);
v___x_2539_ = lean_apply_4(v_toBind_2535_, lean_box(0), lean_box(0), v___x_2538_, v___f_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2540_, lean_object* v_p_2541_, lean_object* v_xs_2542_){
_start:
{
lean_object* v_toApplicative_2543_; lean_object* v_toBind_2544_; lean_object* v_toPure_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___f_2548_; uint8_t v___x_2549_; 
v_toApplicative_2543_ = lean_ctor_get(v_inst_2540_, 0);
v_toBind_2544_ = lean_ctor_get(v_inst_2540_, 1);
lean_inc(v_toBind_2544_);
v_toPure_2545_ = lean_ctor_get(v_toApplicative_2543_, 1);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_array_get_size(v_xs_2542_);
lean_inc(v_toPure_2545_);
v___f_2548_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2548_, 0, v_toPure_2545_);
v___x_2549_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_inc(v_toPure_2545_);
lean_dec_ref(v_xs_2542_);
lean_dec(v_p_2541_);
lean_dec_ref(v_inst_2540_);
v___x_2550_ = lean_box(v___x_2549_);
v___x_2551_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2550_);
v___x_2552_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2551_, v___f_2548_);
return v___x_2552_;
}
else
{
if (v___x_2549_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc(v_toPure_2545_);
lean_dec_ref(v_xs_2542_);
lean_dec(v_p_2541_);
lean_dec_ref(v_inst_2540_);
v___x_2553_ = lean_box(v___x_2549_);
v___x_2554_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2553_);
v___x_2555_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2554_, v___f_2548_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___f_2558_; size_t v___x_2559_; size_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2556_ = lean_box(v___x_2549_);
lean_inc(v_toPure_2545_);
v___f_2557_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2557_, 0, v_toPure_2545_);
lean_closure_set(v___f_2557_, 1, v___x_2556_);
lean_inc(v_toBind_2544_);
v___f_2558_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2558_, 0, v_p_2541_);
lean_closure_set(v___f_2558_, 1, v_toBind_2544_);
lean_closure_set(v___f_2558_, 2, v___f_2557_);
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = lean_usize_of_nat(v___x_2547_);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2540_, v___f_2558_, v_xs_2542_, v___x_2559_, v___x_2560_);
v___x_2562_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2561_, v___f_2548_);
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2563_, lean_object* v_00_u03b1_2564_, lean_object* v_n_2565_, lean_object* v_inst_2566_, lean_object* v_p_2567_, lean_object* v_xs_2568_){
_start:
{
lean_object* v_toApplicative_2569_; lean_object* v_toBind_2570_; lean_object* v_toPure_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; uint8_t v___x_2575_; 
v_toApplicative_2569_ = lean_ctor_get(v_inst_2566_, 0);
v_toBind_2570_ = lean_ctor_get(v_inst_2566_, 1);
lean_inc(v_toBind_2570_);
v_toPure_2571_ = lean_ctor_get(v_toApplicative_2569_, 1);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = lean_array_get_size(v_xs_2568_);
lean_inc(v_toPure_2571_);
v___f_2574_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2574_, 0, v_toPure_2571_);
v___x_2575_ = lean_nat_dec_lt(v___x_2572_, v___x_2573_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_inc(v_toPure_2571_);
lean_dec_ref(v_xs_2568_);
lean_dec(v_p_2567_);
lean_dec_ref(v_inst_2566_);
v___x_2576_ = lean_box(v___x_2575_);
v___x_2577_ = lean_apply_2(v_toPure_2571_, lean_box(0), v___x_2576_);
v___x_2578_ = lean_apply_4(v_toBind_2570_, lean_box(0), lean_box(0), v___x_2577_, v___f_2574_);
return v___x_2578_;
}
else
{
if (v___x_2575_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_inc(v_toPure_2571_);
lean_dec_ref(v_xs_2568_);
lean_dec(v_p_2567_);
lean_dec_ref(v_inst_2566_);
v___x_2579_ = lean_box(v___x_2575_);
v___x_2580_ = lean_apply_2(v_toPure_2571_, lean_box(0), v___x_2579_);
v___x_2581_ = lean_apply_4(v_toBind_2570_, lean_box(0), lean_box(0), v___x_2580_, v___f_2574_);
return v___x_2581_;
}
else
{
lean_object* v___x_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; size_t v___x_2585_; size_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2582_ = lean_box(v___x_2575_);
lean_inc(v_toPure_2571_);
v___f_2583_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2583_, 0, v_toPure_2571_);
lean_closure_set(v___f_2583_, 1, v___x_2582_);
lean_inc(v_toBind_2570_);
v___f_2584_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2584_, 0, v_p_2567_);
lean_closure_set(v___f_2584_, 1, v_toBind_2570_);
lean_closure_set(v___f_2584_, 2, v___f_2583_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = lean_usize_of_nat(v___x_2573_);
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2566_, v___f_2584_, v_xs_2568_, v___x_2585_, v___x_2586_);
v___x_2588_ = lean_apply_4(v_toBind_2570_, lean_box(0), lean_box(0), v___x_2587_, v___f_2574_);
return v___x_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2589_, lean_object* v_00_u03b1_2590_, lean_object* v_n_2591_, lean_object* v_inst_2592_, lean_object* v_p_2593_, lean_object* v_xs_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Vector_allM(v_m_2589_, v_00_u03b1_2590_, v_n_2591_, v_inst_2592_, v_p_2593_, v_xs_2594_);
lean_dec(v_n_2591_);
return v_res_2595_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2596_, lean_object* v_x_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_apply_1(v_p_2596_, v_x_2597_);
v___x_2599_ = lean_unbox(v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2600_, lean_object* v_x_2601_){
_start:
{
uint8_t v_res_2602_; lean_object* v_r_2603_; 
v_res_2602_ = l_Vector_any___redArg___lam__0(v_p_2600_, v_x_2601_);
v_r_2603_ = lean_box(v_res_2602_);
return v_r_2603_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2604_, lean_object* v_p_2605_){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_array_get_size(v_xs_2604_);
v___x_2608_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2609_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
if (v___x_2609_ == 0)
{
lean_dec_ref(v_p_2605_);
lean_dec_ref(v_xs_2604_);
return v___x_2609_;
}
else
{
if (v___x_2609_ == 0)
{
lean_dec_ref(v_p_2605_);
lean_dec_ref(v_xs_2604_);
return v___x_2609_;
}
else
{
lean_object* v___f_2610_; size_t v___x_2611_; size_t v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___f_2610_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2610_, 0, v_p_2605_);
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = lean_usize_of_nat(v___x_2607_);
v___x_2613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2608_, v___f_2610_, v_xs_2604_, v___x_2611_, v___x_2612_);
v___x_2614_ = lean_unbox(v___x_2613_);
lean_dec(v___x_2613_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2615_, lean_object* v_p_2616_){
_start:
{
uint8_t v_res_2617_; lean_object* v_r_2618_; 
v_res_2617_ = l_Vector_any___redArg(v_xs_2615_, v_p_2616_);
v_r_2618_ = lean_box(v_res_2617_);
return v_r_2618_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2619_, lean_object* v_n_2620_, lean_object* v_xs_2621_, lean_object* v_p_2622_){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2623_ = lean_unsigned_to_nat(0u);
v___x_2624_ = lean_array_get_size(v_xs_2621_);
v___x_2625_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2626_ = lean_nat_dec_lt(v___x_2623_, v___x_2624_);
if (v___x_2626_ == 0)
{
lean_dec_ref(v_p_2622_);
lean_dec_ref(v_xs_2621_);
return v___x_2626_;
}
else
{
if (v___x_2626_ == 0)
{
lean_dec_ref(v_p_2622_);
lean_dec_ref(v_xs_2621_);
return v___x_2626_;
}
else
{
lean_object* v___f_2627_; size_t v___x_2628_; size_t v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___f_2627_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2627_, 0, v_p_2622_);
v___x_2628_ = ((size_t)0ULL);
v___x_2629_ = lean_usize_of_nat(v___x_2624_);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2625_, v___f_2627_, v_xs_2621_, v___x_2628_, v___x_2629_);
v___x_2631_ = lean_unbox(v___x_2630_);
lean_dec(v___x_2630_);
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_n_2633_, lean_object* v_xs_2634_, lean_object* v_p_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Vector_any(v_00_u03b1_2632_, v_n_2633_, v_xs_2634_, v_p_2635_);
lean_dec(v_n_2633_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2638_, uint8_t v___x_2639_, lean_object* v_v_2640_){
_start:
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = lean_apply_1(v_p_2638_, v_v_2640_);
v___x_2642_ = lean_unbox(v___x_2641_);
if (v___x_2642_ == 0)
{
return v___x_2639_;
}
else
{
uint8_t v___x_2643_; 
v___x_2643_ = 0;
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2644_, lean_object* v___x_2645_, lean_object* v_v_2646_){
_start:
{
uint8_t v___x_75__boxed_2647_; uint8_t v_res_2648_; lean_object* v_r_2649_; 
v___x_75__boxed_2647_ = lean_unbox(v___x_2645_);
v_res_2648_ = l_Vector_all___redArg___lam__0(v_p_2644_, v___x_75__boxed_2647_, v_v_2646_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2650_, lean_object* v_p_2651_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2652_ = lean_unsigned_to_nat(0u);
v___x_2653_ = lean_array_get_size(v_xs_2650_);
v___x_2654_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2655_ = lean_nat_dec_lt(v___x_2652_, v___x_2653_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
lean_dec_ref(v_p_2651_);
lean_dec_ref(v_xs_2650_);
v___x_2656_ = 1;
return v___x_2656_;
}
else
{
if (v___x_2655_ == 0)
{
lean_dec_ref(v_p_2651_);
lean_dec_ref(v_xs_2650_);
return v___x_2655_;
}
else
{
lean_object* v___x_2657_; lean_object* v___f_2658_; size_t v___x_2659_; size_t v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2657_ = lean_box(v___x_2655_);
v___f_2658_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2658_, 0, v_p_2651_);
lean_closure_set(v___f_2658_, 1, v___x_2657_);
v___x_2659_ = ((size_t)0ULL);
v___x_2660_ = lean_usize_of_nat(v___x_2653_);
v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2654_, v___f_2658_, v_xs_2650_, v___x_2659_, v___x_2660_);
v___x_2662_ = lean_unbox(v___x_2661_);
lean_dec(v___x_2661_);
if (v___x_2662_ == 0)
{
return v___x_2655_;
}
else
{
uint8_t v___x_2663_; 
v___x_2663_ = 0;
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2664_, lean_object* v_p_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_Vector_all___redArg(v_xs_2664_, v_p_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2668_, lean_object* v_n_2669_, lean_object* v_xs_2670_, lean_object* v_p_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get_size(v_xs_2670_);
v___x_2674_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2675_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
if (v___x_2675_ == 0)
{
uint8_t v___x_2676_; 
lean_dec_ref(v_p_2671_);
lean_dec_ref(v_xs_2670_);
v___x_2676_ = 1;
return v___x_2676_;
}
else
{
if (v___x_2675_ == 0)
{
lean_dec_ref(v_p_2671_);
lean_dec_ref(v_xs_2670_);
return v___x_2675_;
}
else
{
lean_object* v___x_2677_; lean_object* v___f_2678_; size_t v___x_2679_; size_t v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2677_ = lean_box(v___x_2675_);
v___f_2678_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2678_, 0, v_p_2671_);
lean_closure_set(v___f_2678_, 1, v___x_2677_);
v___x_2679_ = ((size_t)0ULL);
v___x_2680_ = lean_usize_of_nat(v___x_2673_);
v___x_2681_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2674_, v___f_2678_, v_xs_2670_, v___x_2679_, v___x_2680_);
v___x_2682_ = lean_unbox(v___x_2681_);
lean_dec(v___x_2681_);
if (v___x_2682_ == 0)
{
return v___x_2675_;
}
else
{
uint8_t v___x_2683_; 
v___x_2683_ = 0;
return v___x_2683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2684_, lean_object* v_n_2685_, lean_object* v_xs_2686_, lean_object* v_p_2687_){
_start:
{
uint8_t v_res_2688_; lean_object* v_r_2689_; 
v_res_2688_ = l_Vector_all(v_00_u03b1_2684_, v_n_2685_, v_xs_2686_, v_p_2687_);
lean_dec(v_n_2685_);
v_r_2689_ = lean_box(v_res_2688_);
return v_r_2689_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2690_, lean_object* v_x1_2691_, lean_object* v_x2_2692_){
_start:
{
lean_object* v___x_2693_; uint8_t v___x_2694_; 
v___x_2693_ = lean_apply_1(v_p_2690_, v_x1_2691_);
v___x_2694_ = lean_unbox(v___x_2693_);
if (v___x_2694_ == 0)
{
lean_inc(v_x2_2692_);
return v_x2_2692_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_nat_add(v_x2_2692_, v___x_2695_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2697_, lean_object* v_x1_2698_, lean_object* v_x2_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Vector_countP___redArg___lam__0(v_p_2697_, v_x1_2698_, v_x2_2699_);
lean_dec(v_x2_2699_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2701_, lean_object* v_xs_2702_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_array_get_size(v_xs_2702_);
v___x_2705_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2706_ = lean_nat_dec_lt(v___x_2703_, v___x_2704_);
if (v___x_2706_ == 0)
{
lean_dec_ref(v_xs_2702_);
lean_dec_ref(v_p_2701_);
return v___x_2703_;
}
else
{
lean_object* v___f_2707_; size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___f_2707_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2707_, 0, v_p_2701_);
v___x_2708_ = lean_usize_of_nat(v___x_2704_);
v___x_2709_ = ((size_t)0ULL);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2705_, v___f_2707_, v_xs_2702_, v___x_2708_, v___x_2709_, v___x_2703_);
return v___x_2710_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2711_, lean_object* v_n_2712_, lean_object* v_p_2713_, lean_object* v_xs_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_array_get_size(v_xs_2714_);
v___x_2717_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2718_ = lean_nat_dec_lt(v___x_2715_, v___x_2716_);
if (v___x_2718_ == 0)
{
lean_dec_ref(v_xs_2714_);
lean_dec_ref(v_p_2713_);
return v___x_2715_;
}
else
{
lean_object* v___f_2719_; size_t v___x_2720_; size_t v___x_2721_; lean_object* v___x_2722_; 
v___f_2719_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2719_, 0, v_p_2713_);
v___x_2720_ = lean_usize_of_nat(v___x_2716_);
v___x_2721_ = ((size_t)0ULL);
v___x_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2717_, v___f_2719_, v_xs_2714_, v___x_2720_, v___x_2721_, v___x_2715_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_n_2724_, lean_object* v_p_2725_, lean_object* v_xs_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Vector_countP(v_00_u03b1_2723_, v_n_2724_, v_p_2725_, v_xs_2726_);
lean_dec(v_n_2724_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2728_, lean_object* v_a_2729_, lean_object* v_x1_2730_, lean_object* v_x2_2731_){
_start:
{
lean_object* v___x_2732_; uint8_t v___x_2733_; 
v___x_2732_ = lean_apply_2(v_inst_2728_, v_x1_2730_, v_a_2729_);
v___x_2733_ = lean_unbox(v___x_2732_);
if (v___x_2733_ == 0)
{
lean_inc(v_x2_2731_);
return v_x2_2731_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_x2_2731_, v___x_2734_);
return v___x_2735_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2736_, lean_object* v_a_2737_, lean_object* v_x1_2738_, lean_object* v_x2_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Vector_count___redArg___lam__0(v_inst_2736_, v_a_2737_, v_x1_2738_, v_x2_2739_);
lean_dec(v_x2_2739_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2741_, lean_object* v_a_2742_, lean_object* v_xs_2743_){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2744_ = lean_unsigned_to_nat(0u);
v___x_2745_ = lean_array_get_size(v_xs_2743_);
v___x_2746_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2747_ = lean_nat_dec_lt(v___x_2744_, v___x_2745_);
if (v___x_2747_ == 0)
{
lean_dec_ref(v_xs_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_inst_2741_);
return v___x_2744_;
}
else
{
lean_object* v___f_2748_; size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; 
v___f_2748_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2748_, 0, v_inst_2741_);
lean_closure_set(v___f_2748_, 1, v_a_2742_);
v___x_2749_ = lean_usize_of_nat(v___x_2745_);
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2746_, v___f_2748_, v_xs_2743_, v___x_2749_, v___x_2750_, v___x_2744_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2752_, lean_object* v_n_2753_, lean_object* v_inst_2754_, lean_object* v_a_2755_, lean_object* v_xs_2756_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = lean_unsigned_to_nat(0u);
v___x_2758_ = lean_array_get_size(v_xs_2756_);
v___x_2759_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2760_ = lean_nat_dec_lt(v___x_2757_, v___x_2758_);
if (v___x_2760_ == 0)
{
lean_dec_ref(v_xs_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_inst_2754_);
return v___x_2757_;
}
else
{
lean_object* v___f_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v___f_2761_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2761_, 0, v_inst_2754_);
lean_closure_set(v___f_2761_, 1, v_a_2755_);
v___x_2762_ = lean_usize_of_nat(v___x_2758_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2759_, v___f_2761_, v_xs_2756_, v___x_2762_, v___x_2763_, v___x_2757_);
return v___x_2764_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_n_2766_, lean_object* v_inst_2767_, lean_object* v_a_2768_, lean_object* v_xs_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_Vector_count(v_00_u03b1_2765_, v_n_2766_, v_inst_2767_, v_a_2768_, v_xs_2769_);
lean_dec(v_n_2766_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2771_, lean_object* v_xs_2772_, lean_object* v_a_2773_, lean_object* v_b_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Array_replace___redArg(v_inst_2771_, v_xs_2772_, v_a_2773_, v_b_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2776_, lean_object* v_n_2777_, lean_object* v_inst_2778_, lean_object* v_xs_2779_, lean_object* v_a_2780_, lean_object* v_b_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Array_replace___redArg(v_inst_2778_, v_xs_2779_, v_a_2780_, v_b_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_n_2784_, lean_object* v_inst_2785_, lean_object* v_xs_2786_, lean_object* v_a_2787_, lean_object* v_b_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Vector_replace(v_00_u03b1_2783_, v_n_2784_, v_inst_2785_, v_xs_2786_, v_a_2787_, v_b_2788_);
lean_dec(v_n_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2790_, lean_object* v_x1_2791_, lean_object* v_x2_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_apply_2(v_inst_2790_, v_x1_2791_, v_x2_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2794_, lean_object* v_inst_2795_, lean_object* v_xs_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2797_ = lean_array_get_size(v_xs_2796_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2800_ = lean_nat_dec_lt(v___x_2798_, v___x_2797_);
if (v___x_2800_ == 0)
{
lean_dec_ref(v_xs_2796_);
lean_dec(v_inst_2794_);
return v_inst_2795_;
}
else
{
lean_object* v___f_2801_; size_t v___x_2802_; size_t v___x_2803_; lean_object* v___x_2804_; 
v___f_2801_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2801_, 0, v_inst_2794_);
v___x_2802_ = lean_usize_of_nat(v___x_2797_);
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2799_, v___f_2801_, v_xs_2796_, v___x_2802_, v___x_2803_, v_inst_2795_);
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2805_, lean_object* v_n_2806_, lean_object* v_inst_2807_, lean_object* v_inst_2808_, lean_object* v_xs_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2810_ = lean_array_get_size(v_xs_2809_);
v___x_2811_ = lean_unsigned_to_nat(0u);
v___x_2812_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2813_ = lean_nat_dec_lt(v___x_2811_, v___x_2810_);
if (v___x_2813_ == 0)
{
lean_dec_ref(v_xs_2809_);
lean_dec(v_inst_2807_);
return v_inst_2808_;
}
else
{
lean_object* v___f_2814_; size_t v___x_2815_; size_t v___x_2816_; lean_object* v___x_2817_; 
v___f_2814_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2814_, 0, v_inst_2807_);
v___x_2815_ = lean_usize_of_nat(v___x_2810_);
v___x_2816_ = ((size_t)0ULL);
v___x_2817_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2812_, v___f_2814_, v_xs_2809_, v___x_2815_, v___x_2816_, v_inst_2808_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2818_, lean_object* v_n_2819_, lean_object* v_inst_2820_, lean_object* v_inst_2821_, lean_object* v_xs_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Vector_sum(v_00_u03b1_2818_, v_n_2819_, v_inst_2820_, v_inst_2821_, v_xs_2822_);
lean_dec(v_n_2819_);
return v_res_2823_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_xs_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2827_ = lean_array_get_size(v_xs_2826_);
v___x_2828_ = lean_unsigned_to_nat(0u);
v___x_2829_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2830_ = lean_nat_dec_lt(v___x_2828_, v___x_2827_);
if (v___x_2830_ == 0)
{
lean_dec_ref(v_xs_2826_);
lean_dec(v_inst_2824_);
return v_inst_2825_;
}
else
{
lean_object* v___f_2831_; size_t v___x_2832_; size_t v___x_2833_; lean_object* v___x_2834_; 
v___f_2831_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2831_, 0, v_inst_2824_);
v___x_2832_ = lean_usize_of_nat(v___x_2827_);
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2829_, v___f_2831_, v_xs_2826_, v___x_2832_, v___x_2833_, v_inst_2825_);
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2835_, lean_object* v_n_2836_, lean_object* v_inst_2837_, lean_object* v_inst_2838_, lean_object* v_xs_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2840_ = lean_array_get_size(v_xs_2839_);
v___x_2841_ = lean_unsigned_to_nat(0u);
v___x_2842_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2843_ = lean_nat_dec_lt(v___x_2841_, v___x_2840_);
if (v___x_2843_ == 0)
{
lean_dec_ref(v_xs_2839_);
lean_dec(v_inst_2837_);
return v_inst_2838_;
}
else
{
lean_object* v___f_2844_; size_t v___x_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
v___f_2844_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2844_, 0, v_inst_2837_);
v___x_2845_ = lean_usize_of_nat(v___x_2840_);
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2842_, v___f_2844_, v_xs_2839_, v___x_2845_, v___x_2846_, v_inst_2838_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2848_, lean_object* v_n_2849_, lean_object* v_inst_2850_, lean_object* v_inst_2851_, lean_object* v_xs_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Vector_prod(v_00_u03b1_2848_, v_n_2849_, v_inst_2850_, v_inst_2851_, v_xs_2852_);
lean_dec(v_n_2849_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2854_, lean_object* v_n_2855_, lean_object* v_a_2856_, lean_object* v_xs_2857_){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = lean_nat_sub(v_n_2855_, v_m_2854_);
v___x_2859_ = lean_mk_array(v___x_2858_, v_a_2856_);
v___x_2860_ = l_Array_append___redArg(v___x_2859_, v_xs_2857_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2861_, lean_object* v_n_2862_, lean_object* v_a_2863_, lean_object* v_xs_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Vector_leftpad___redArg(v_m_2861_, v_n_2862_, v_a_2863_, v_xs_2864_);
lean_dec_ref(v_xs_2864_);
lean_dec(v_n_2862_);
lean_dec(v_m_2861_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2866_, lean_object* v_m_2867_, lean_object* v_n_2868_, lean_object* v_a_2869_, lean_object* v_xs_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_nat_sub(v_n_2868_, v_m_2867_);
v___x_2872_ = lean_mk_array(v___x_2871_, v_a_2869_);
v___x_2873_ = l_Array_append___redArg(v___x_2872_, v_xs_2870_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2874_, lean_object* v_m_2875_, lean_object* v_n_2876_, lean_object* v_a_2877_, lean_object* v_xs_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Vector_leftpad(v_00_u03b1_2874_, v_m_2875_, v_n_2876_, v_a_2877_, v_xs_2878_);
lean_dec_ref(v_xs_2878_);
lean_dec(v_n_2876_);
lean_dec(v_m_2875_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2880_, lean_object* v_n_2881_, lean_object* v_a_2882_, lean_object* v_xs_2883_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2884_ = lean_nat_sub(v_n_2881_, v_m_2880_);
v___x_2885_ = lean_mk_array(v___x_2884_, v_a_2882_);
v___x_2886_ = l_Array_append___redArg(v_xs_2883_, v___x_2885_);
lean_dec_ref(v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2887_, lean_object* v_n_2888_, lean_object* v_a_2889_, lean_object* v_xs_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Vector_rightpad___redArg(v_m_2887_, v_n_2888_, v_a_2889_, v_xs_2890_);
lean_dec(v_n_2888_);
lean_dec(v_m_2887_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2892_, lean_object* v_m_2893_, lean_object* v_n_2894_, lean_object* v_a_2895_, lean_object* v_xs_2896_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_nat_sub(v_n_2894_, v_m_2893_);
v___x_2898_ = lean_mk_array(v___x_2897_, v_a_2895_);
v___x_2899_ = l_Array_append___redArg(v_xs_2896_, v___x_2898_);
lean_dec_ref(v___x_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2900_, lean_object* v_m_2901_, lean_object* v_n_2902_, lean_object* v_a_2903_, lean_object* v_xs_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Vector_rightpad(v_00_u03b1_2900_, v_m_2901_, v_n_2902_, v_a_2903_, v_xs_2904_);
lean_dec(v_n_2902_);
lean_dec(v_m_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2906_, lean_object* v_a_2907_, lean_object* v_h_2908_, lean_object* v_b_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_apply_3(v_f_2906_, v_a_2907_, lean_box(0), v_b_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_xs_2913_, lean_object* v_b_2914_, lean_object* v_f_2915_){
_start:
{
lean_object* v___f_2916_; size_t v_sz_2917_; size_t v___x_2918_; lean_object* v___x_2919_; 
v___f_2916_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2916_, 0, v_f_2915_);
v_sz_2917_ = lean_array_size(v_xs_2913_);
v___x_2918_ = ((size_t)0ULL);
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2911_, v_xs_2913_, v___f_2916_, v_sz_2917_, v___x_2918_, v_b_2914_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2920_){
_start:
{
lean_object* v___f_2921_; 
v___f_2921_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2921_, 0, v_inst_2920_);
return v___f_2921_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2922_, lean_object* v_00_u03b1_2923_, lean_object* v_n_2924_, lean_object* v_inst_2925_){
_start:
{
lean_object* v___f_2926_; 
v___f_2926_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2926_, 0, v_inst_2925_);
return v___f_2926_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2927_, lean_object* v_00_u03b1_2928_, lean_object* v_n_2929_, lean_object* v_inst_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2927_, v_00_u03b1_2928_, v_n_2929_, v_inst_2930_);
lean_dec(v_n_2929_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2932_, lean_object* v_inst_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2934_, 0, lean_box(0));
lean_closure_set(v___x_2934_, 1, lean_box(0));
lean_closure_set(v___x_2934_, 2, v_n_2932_);
lean_closure_set(v___x_2934_, 3, v_inst_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2935_, lean_object* v_00_u03b1_2936_, lean_object* v_n_2937_, lean_object* v_inst_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2939_, 0, lean_box(0));
lean_closure_set(v___x_2939_, 1, lean_box(0));
lean_closure_set(v___x_2939_, 2, v_n_2937_);
lean_closure_set(v___x_2939_, 3, v_inst_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg(){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_box(0);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___redArg___boxed(lean_object* v___dummy_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Vector_instLT___redArg();
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2944_, lean_object* v_n_2945_, lean_object* v_inst_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = lean_box(0);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2948_, lean_object* v_n_2949_, lean_object* v_inst_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Vector_instLT(v_00_u03b1_2948_, v_n_2949_, v_inst_2950_);
lean_dec(v_n_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg(){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = lean_box(0);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___redArg___boxed(lean_object* v___dummy_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Vector_instLE___redArg();
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2956_, lean_object* v_n_2957_, lean_object* v_inst_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = lean_box(0);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_n_2961_, lean_object* v_inst_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Vector_instLE(v_00_u03b1_2960_, v_n_2961_, v_inst_2962_);
lean_dec(v_n_2961_);
return v_res_2963_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2971_ = l_Lean_mkAtom(v___x_2970_);
return v___x_2971_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2973_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2974_ = lean_array_push(v___x_2973_, v___x_2972_);
return v___x_2974_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_2988_ = l_Lean_mkAtom(v___x_2987_);
return v___x_2988_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_2990_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2991_ = lean_array_push(v___x_2990_, v___x_2989_);
return v___x_2991_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l_Vector_lex___auto__1___closed__14));
v___x_3006_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3007_ = lean_array_push(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3008_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3009_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3010_ = lean_box(2);
v___x_3011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3008_);
return v___x_3011_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3013_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3014_ = lean_array_push(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3015_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3016_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3017_ = lean_box(2);
v___x_3018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
lean_ctor_set(v___x_3018_, 1, v___x_3016_);
lean_ctor_set(v___x_3018_, 2, v___x_3015_);
return v___x_3018_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3020_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3021_ = lean_array_push(v___x_3020_, v___x_3019_);
return v___x_3021_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__25(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3033_ = l_Lean_mkAtom(v___x_3032_);
return v___x_3033_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_obj_once(&l_Vector_lex___auto__1___closed__25, &l_Vector_lex___auto__1___closed__25_once, _init_l_Vector_lex___auto__1___closed__25);
v___x_3035_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3036_ = lean_array_push(v___x_3035_, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3038_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3037_);
return v___x_3039_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3040_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3041_ = ((lean_object*)(l_Vector_lex___auto__1___closed__23));
v___x_3042_ = lean_box(2);
v___x_3043_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
lean_ctor_set(v___x_3043_, 1, v___x_3041_);
lean_ctor_set(v___x_3043_, 2, v___x_3040_);
return v___x_3043_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3045_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3046_ = lean_array_push(v___x_3045_, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l_Vector_lex___auto__1___closed__30));
v___x_3049_ = l_Lean_mkAtom(v___x_3048_);
return v___x_3049_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_obj_once(&l_Vector_lex___auto__1___closed__31, &l_Vector_lex___auto__1___closed__31_once, _init_l_Vector_lex___auto__1___closed__31);
v___x_3051_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3052_ = lean_array_push(v___x_3051_, v___x_3050_);
return v___x_3052_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3054_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3055_ = lean_array_push(v___x_3054_, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3057_ = ((lean_object*)(l_Vector_lex___auto__1___closed__21));
v___x_3058_ = lean_box(2);
v___x_3059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
lean_ctor_set(v___x_3059_, 1, v___x_3057_);
lean_ctor_set(v___x_3059_, 2, v___x_3056_);
return v___x_3059_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3061_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3062_ = lean_array_push(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3064_ = l_Lean_mkAtom(v___x_3063_);
return v___x_3064_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3066_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3067_ = lean_array_push(v___x_3066_, v___x_3065_);
return v___x_3067_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3068_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3069_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3070_ = lean_box(2);
v___x_3071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
lean_ctor_set(v___x_3071_, 1, v___x_3069_);
lean_ctor_set(v___x_3071_, 2, v___x_3068_);
return v___x_3071_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3073_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3074_ = lean_array_push(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3075_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3076_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3077_ = lean_box(2);
v___x_3078_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3076_);
lean_ctor_set(v___x_3078_, 2, v___x_3075_);
return v___x_3078_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3080_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3081_ = lean_array_push(v___x_3080_, v___x_3079_);
return v___x_3081_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3083_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3084_ = lean_box(2);
v___x_3085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
lean_ctor_set(v___x_3085_, 2, v___x_3082_);
return v___x_3085_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3087_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3088_ = lean_array_push(v___x_3087_, v___x_3086_);
return v___x_3088_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3090_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3091_ = lean_box(2);
v___x_3092_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3094_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3095_ = lean_array_push(v___x_3094_, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3096_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3097_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3098_ = lean_box(2);
v___x_3099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
lean_ctor_set(v___x_3099_, 1, v___x_3097_);
lean_ctor_set(v___x_3099_, 2, v___x_3096_);
return v___x_3099_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
return v___x_3100_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(lean_object* v_n_3101_, lean_object* v_inst_3102_, lean_object* v_xs_3103_, lean_object* v_ys_3104_, lean_object* v_lt_3105_, lean_object* v_i_3106_){
_start:
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_nat_dec_le(v_n_3101_, v_i_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3108_ = lean_array_fget_borrowed(v_xs_3103_, v_i_3106_);
v___x_3109_ = lean_array_fget_borrowed(v_ys_3104_, v_i_3106_);
lean_inc_ref(v_lt_3105_);
lean_inc(v___x_3109_);
lean_inc(v___x_3108_);
v___x_3110_ = lean_apply_2(v_lt_3105_, v___x_3108_, v___x_3109_);
v___x_3111_ = lean_unbox(v___x_3110_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
lean_inc_ref(v_inst_3102_);
lean_inc(v___x_3109_);
lean_inc(v___x_3108_);
v___x_3112_ = lean_apply_2(v_inst_3102_, v___x_3108_, v___x_3109_);
v___x_3113_ = lean_unbox(v___x_3112_);
if (v___x_3113_ == 0)
{
uint8_t v___x_3114_; 
lean_dec(v_i_3106_);
lean_dec_ref(v_lt_3105_);
lean_dec_ref(v_inst_3102_);
v___x_3114_ = lean_unbox(v___x_3112_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_unsigned_to_nat(1u);
v___x_3116_ = lean_nat_add(v_i_3106_, v___x_3115_);
lean_dec(v_i_3106_);
v_i_3106_ = v___x_3116_;
goto _start;
}
}
else
{
uint8_t v___x_3118_; 
lean_dec(v_i_3106_);
lean_dec_ref(v_lt_3105_);
lean_dec_ref(v_inst_3102_);
v___x_3118_ = lean_unbox(v___x_3110_);
return v___x_3118_;
}
}
else
{
uint8_t v___x_3119_; 
lean_dec(v_i_3106_);
lean_dec_ref(v_lt_3105_);
lean_dec_ref(v_inst_3102_);
v___x_3119_ = 0;
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg___boxed(lean_object* v_n_3120_, lean_object* v_inst_3121_, lean_object* v_xs_3122_, lean_object* v_ys_3123_, lean_object* v_lt_3124_, lean_object* v_i_3125_){
_start:
{
uint8_t v_res_3126_; lean_object* v_r_3127_; 
v_res_3126_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3120_, v_inst_3121_, v_xs_3122_, v_ys_3123_, v_lt_3124_, v_i_3125_);
lean_dec_ref(v_ys_3123_);
lean_dec_ref(v_xs_3122_);
lean_dec(v_n_3120_);
v_r_3127_ = lean_box(v_res_3126_);
return v_r_3127_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Vector_Basic_0__Vector_lex_go(lean_object* v_00_u03b1_3128_, lean_object* v_n_3129_, lean_object* v_inst_3130_, lean_object* v_xs_3131_, lean_object* v_ys_3132_, lean_object* v_lt_3133_, lean_object* v_i_3134_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3129_, v_inst_3130_, v_xs_3131_, v_ys_3132_, v_lt_3133_, v_i_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_lex_go___boxed(lean_object* v_00_u03b1_3136_, lean_object* v_n_3137_, lean_object* v_inst_3138_, lean_object* v_xs_3139_, lean_object* v_ys_3140_, lean_object* v_lt_3141_, lean_object* v_i_3142_){
_start:
{
uint8_t v_res_3143_; lean_object* v_r_3144_; 
v_res_3143_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go(v_00_u03b1_3136_, v_n_3137_, v_inst_3138_, v_xs_3139_, v_ys_3140_, v_lt_3141_, v_i_3142_);
lean_dec_ref(v_ys_3140_);
lean_dec_ref(v_xs_3139_);
lean_dec(v_n_3137_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3145_, lean_object* v_inst_3146_, lean_object* v_xs_3147_, lean_object* v_ys_3148_, lean_object* v_lt_3149_){
_start:
{
lean_object* v___x_3150_; uint8_t v___x_3151_; 
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = l___private_Init_Data_Vector_Basic_0__Vector_lex_go___redArg(v_n_3145_, v_inst_3146_, v_xs_3147_, v_ys_3148_, v_lt_3149_, v___x_3150_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3152_, lean_object* v_inst_3153_, lean_object* v_xs_3154_, lean_object* v_ys_3155_, lean_object* v_lt_3156_){
_start:
{
uint8_t v_res_3157_; lean_object* v_r_3158_; 
v_res_3157_ = l_Vector_lex___redArg(v_n_3152_, v_inst_3153_, v_xs_3154_, v_ys_3155_, v_lt_3156_);
lean_dec_ref(v_ys_3155_);
lean_dec_ref(v_xs_3154_);
lean_dec(v_n_3152_);
v_r_3158_ = lean_box(v_res_3157_);
return v_r_3158_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3159_, lean_object* v_n_3160_, lean_object* v_inst_3161_, lean_object* v_xs_3162_, lean_object* v_ys_3163_, lean_object* v_lt_3164_){
_start:
{
uint8_t v___x_3165_; 
v___x_3165_ = l_Vector_lex___redArg(v_n_3160_, v_inst_3161_, v_xs_3162_, v_ys_3163_, v_lt_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3166_, lean_object* v_n_3167_, lean_object* v_inst_3168_, lean_object* v_xs_3169_, lean_object* v_ys_3170_, lean_object* v_lt_3171_){
_start:
{
uint8_t v_res_3172_; lean_object* v_r_3173_; 
v_res_3172_ = l_Vector_lex(v_00_u03b1_3166_, v_n_3167_, v_inst_3168_, v_xs_3169_, v_ys_3170_, v_lt_3171_);
lean_dec_ref(v_ys_3170_);
lean_dec_ref(v_xs_3169_);
lean_dec(v_n_3167_);
v_r_3173_ = lean_box(v_res_3172_);
return v_r_3173_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Vector_set___auto__1 = _init_l_Vector_set___auto__1();
lean_mark_persistent(l_Vector_set___auto__1);
l_Vector_swap___auto__1 = _init_l_Vector_swap___auto__1();
lean_mark_persistent(l_Vector_swap___auto__1);
l_Vector_swap___auto__3 = _init_l_Vector_swap___auto__3();
lean_mark_persistent(l_Vector_swap___auto__3);
l_Vector_swapAt___auto__1 = _init_l_Vector_swapAt___auto__1();
lean_mark_persistent(l_Vector_swapAt___auto__1);
l_Vector_eraseIdx___auto__1 = _init_l_Vector_eraseIdx___auto__1();
lean_mark_persistent(l_Vector_eraseIdx___auto__1);
l_Vector_insertIdx___auto__1 = _init_l_Vector_insertIdx___auto__1();
lean_mark_persistent(l_Vector_insertIdx___auto__1);
l_Vector_lex___auto__1 = _init_l_Vector_lex___auto__1();
lean_mark_persistent(l_Vector_lex___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
