// Lean compiler output
// Module: Init.Data.Vector.Basic
// Imports: import Init.Data.Array.Nat public import Init.Data.Array.DecidableEq public import Init.Data.Range.Polymorphic.RangeIterator import Init.Data.Array.InsertIdx import Init.Data.Array.MapIdx import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Omega
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
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_zipIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zipWithMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
static const lean_string_object l_instReprVector_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_instReprVector_repr___redArg___closed__0 = (const lean_object*)&l_instReprVector_repr___redArg___closed__0_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_instReprVector_repr___redArg___closed__1 = (const lean_object*)&l_instReprVector_repr___redArg___closed__1_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__1_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__2 = (const lean_object*)&l_instReprVector_repr___redArg___closed__2_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_instReprVector_repr___redArg___closed__2_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__3 = (const lean_object*)&l_instReprVector_repr___redArg___closed__3_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_instReprVector_repr___redArg___closed__4 = (const lean_object*)&l_instReprVector_repr___redArg___closed__4_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__4_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__5 = (const lean_object*)&l_instReprVector_repr___redArg___closed__5_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__3_value),((lean_object*)&l_instReprVector_repr___redArg___closed__5_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__6 = (const lean_object*)&l_instReprVector_repr___redArg___closed__6_value;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__7;
static const lean_string_object l_instReprVector_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_instReprVector_repr___redArg___closed__8 = (const lean_object*)&l_instReprVector_repr___redArg___closed__8_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__8_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__9 = (const lean_object*)&l_instReprVector_repr___redArg___closed__9_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "size_toArray"};
static const lean_object* l_instReprVector_repr___redArg___closed__10 = (const lean_object*)&l_instReprVector_repr___redArg___closed__10_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__10_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__11 = (const lean_object*)&l_instReprVector_repr___redArg___closed__11_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_instReprVector_repr___redArg___closed__12 = (const lean_object*)&l_instReprVector_repr___redArg___closed__12_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__12_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__13 = (const lean_object*)&l_instReprVector_repr___redArg___closed__13_value;
static const lean_string_object l_instReprVector_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_instReprVector_repr___redArg___closed__14 = (const lean_object*)&l_instReprVector_repr___redArg___closed__14_value;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__15;
static lean_once_cell_t l_instReprVector_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprVector_repr___redArg___closed__16;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__0_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__17 = (const lean_object*)&l_instReprVector_repr___redArg___closed__17_value;
static const lean_ctor_object l_instReprVector_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprVector_repr___redArg___closed__14_value)}};
static const lean_object* l_instReprVector_repr___redArg___closed__18 = (const lean_object*)&l_instReprVector_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_instReprVector_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprVector(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__12 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__12_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__13 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__11_value),((lean_object*)&l_instReprVector_repr___redArg___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__13_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__14 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__8_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__14_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__15 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__6_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__15_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__16 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value;
static const lean_string_object l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__17 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__17_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__18 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__4_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__16_value),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__18_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__19 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value;
static const lean_ctor_object l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__19_value)}};
static const lean_object* l_Vector_term_x23v_x5b___x2c_x5d___closed__20 = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
LEAN_EXPORT const lean_object* l_Vector_term_x23v_x5b___x2c_x5d = (const lean_object*)&l_Vector_term_x23v_x5b___x2c_x5d___closed__20_value;
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
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Vector_instGetElemNatLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Vector_instGetElemNatLt___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Vector_instGetElemNatLt___closed__0 = (const lean_object*)&l_Vector_instGetElemNatLt___closed__0_value;
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Vector_lex___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__13;
static lean_once_cell_t l_Vector_lex___auto__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__14;
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
static lean_once_cell_t l_Vector_lex___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__20;
static const lean_string_object l_Vector_lex___auto__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Vector_lex___auto__1___closed__21 = (const lean_object*)&l_Vector_lex___auto__1___closed__21_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector_lex___auto__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Vector_lex___auto__1___closed__22 = (const lean_object*)&l_Vector_lex___auto__1___closed__22_value;
static const lean_string_object l_Vector_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Vector_lex___auto__1___closed__23 = (const lean_object*)&l_Vector_lex___auto__1___closed__23_value;
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_0),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_1),((lean_object*)&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Vector_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Vector_lex___auto__1___closed__24_value_aux_2),((lean_object*)&l_Vector_lex___auto__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Vector_lex___auto__1___closed__24 = (const lean_object*)&l_Vector_lex___auto__1___closed__24_value;
static const lean_string_object l_Vector_lex___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Vector_lex___auto__1___closed__25 = (const lean_object*)&l_Vector_lex___auto__1___closed__25_value;
static lean_once_cell_t l_Vector_lex___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__26;
static lean_once_cell_t l_Vector_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__27;
static lean_once_cell_t l_Vector_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__28;
static lean_once_cell_t l_Vector_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__29;
static lean_once_cell_t l_Vector_lex___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__30;
static const lean_string_object l_Vector_lex___auto__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Vector_lex___auto__1___closed__31 = (const lean_object*)&l_Vector_lex___auto__1___closed__31_value;
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
static lean_once_cell_t l_Vector_lex___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Vector_lex___auto__1___closed__47;
LEAN_EXPORT lean_object* l_Vector_lex___auto__1;
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Vector_lex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Vector_lex___redArg___closed__0 = (const lean_object*)&l_Vector_lex___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_instReprVector_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(11u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_l_instReprVector_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__0));
v___x_27_ = lean_string_length(v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_instReprVector_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__15, &l_instReprVector_repr___redArg___closed__15_once, _init_l_instReprVector_repr___redArg___closed__15);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr___redArg(lean_object* v_inst_34_, lean_object* v_x_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_36_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__5));
v___x_37_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__6));
v___x_38_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__7, &l_instReprVector_repr___redArg___closed__7_once, _init_l_instReprVector_repr___redArg___closed__7);
v___x_39_ = l_Array_repr___redArg(v_inst_34_, v_x_35_);
v___x_40_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_41_);
v___x_43_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_37_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__9));
v___x_45_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_box(1);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__11));
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_36_);
v___x_51_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__13));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_obj_once(&l_instReprVector_repr___redArg___closed__16, &l_instReprVector_repr___redArg___closed__16_once, _init_l_instReprVector_repr___redArg___closed__16);
v___x_54_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__17));
v___x_55_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_52_);
v___x_56_ = ((lean_object*)(l_instReprVector_repr___redArg___closed__18));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_53_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_59_, sizeof(void*)*1, v___x_41_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr(lean_object* v_00_u03b1_60_, lean_object* v_n_61_, lean_object* v_inst_62_, lean_object* v_x_63_, lean_object* v_prec_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_instReprVector_repr___redArg(v_inst_62_, v_x_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_instReprVector_repr___boxed(lean_object* v_00_u03b1_66_, lean_object* v_n_67_, lean_object* v_inst_68_, lean_object* v_x_69_, lean_object* v_prec_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_instReprVector_repr(v_00_u03b1_66_, v_n_67_, v_inst_68_, v_x_69_, v_prec_70_);
lean_dec(v_prec_70_);
lean_dec(v_n_67_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_instReprVector___redArg(lean_object* v_n_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_closure((void*)(l_instReprVector_repr___boxed), 5, 3);
lean_closure_set(v___x_74_, 0, lean_box(0));
lean_closure_set(v___x_74_, 1, v_n_72_);
lean_closure_set(v___x_74_, 2, v_inst_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_instReprVector(lean_object* v_00_u03b1_75_, lean_object* v_n_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_closure((void*)(l_instReprVector_repr___boxed), 5, 3);
lean_closure_set(v___x_78_, 0, lean_box(0));
lean_closure_set(v___x_78_, 1, v_n_76_);
lean_closure_set(v___x_78_, 2, v_inst_77_);
return v___x_78_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq___redArg(lean_object* v_inst_79_, lean_object* v_x_80_, lean_object* v_x_81_){
_start:
{
uint8_t v___x_82_; 
v___x_82_ = l_Array_instDecidableEqImpl___redArg(v_inst_79_, v_x_80_, v_x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___redArg___boxed(lean_object* v_inst_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_instDecidableEqVector_decEq___redArg(v_inst_83_, v_x_84_, v_x_85_);
lean_dec_ref(v_x_85_);
lean_dec_ref(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector_decEq(lean_object* v_00_u03b1_88_, lean_object* v_n_89_, lean_object* v_inst_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_Array_instDecidableEqImpl___redArg(v_inst_90_, v_x_91_, v_x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector_decEq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_n_95_, lean_object* v_inst_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v_res_99_; lean_object* v_r_100_; 
v_res_99_ = l_instDecidableEqVector_decEq(v_00_u03b1_94_, v_n_95_, v_inst_96_, v_x_97_, v_x_98_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
lean_dec(v_n_95_);
v_r_100_ = lean_box(v_res_99_);
return v_r_100_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector___redArg(lean_object* v_inst_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = l_Array_instDecidableEqImpl___redArg(v_inst_101_, v_x_102_, v_x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___redArg___boxed(lean_object* v_inst_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_instDecidableEqVector___redArg(v_inst_105_, v_x_106_, v_x_107_);
lean_dec_ref(v_x_107_);
lean_dec_ref(v_x_106_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqVector(lean_object* v_00_u03b1_110_, lean_object* v_n_111_, lean_object* v_inst_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Array_instDecidableEqImpl___redArg(v_inst_112_, v_x_113_, v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqVector___boxed(lean_object* v_00_u03b1_116_, lean_object* v_n_117_, lean_object* v_inst_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_instDecidableEqVector(v_00_u03b1_116_, v_n_117_, v_inst_118_, v_x_119_, v_x_120_);
lean_dec_ref(v_x_120_);
lean_dec_ref(v_x_119_);
lean_dec(v_n_117_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg(lean_object* v_xs_123_){
_start:
{
lean_inc_ref(v_xs_123_);
return v_xs_123_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___redArg___boxed(lean_object* v_xs_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Array_toVector___redArg(v_xs_124_);
lean_dec_ref(v_xs_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector(lean_object* v_00_u03b1_126_, lean_object* v_xs_127_){
_start:
{
lean_inc_ref(v_xs_127_);
return v_xs_127_;
}
}
LEAN_EXPORT lean_object* l_Array_toVector___boxed(lean_object* v_00_u03b1_128_, lean_object* v_xs_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Array_toVector(v_00_u03b1_128_, v_xs_129_);
lean_dec_ref(v_xs_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg(lean_object* v_n_131_){
_start:
{
lean_inc(v_n_131_);
return v_n_131_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___redArg___boxed(lean_object* v_n_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Vector_size___redArg(v_n_132_);
lean_dec(v_n_132_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Vector_size(lean_object* v_00_u03b1_134_, lean_object* v_n_135_, lean_object* v_x_136_){
_start:
{
lean_inc(v_n_135_);
return v_n_135_;
}
}
LEAN_EXPORT lean_object* l_Vector_size___boxed(lean_object* v_00_u03b1_137_, lean_object* v_n_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Vector_size(v_00_u03b1_137_, v_n_138_, v_x_139_);
lean_dec_ref(v_x_139_);
lean_dec(v_n_138_);
return v_res_140_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__5));
v___x_199_ = l_String_toRawSubstring_x27(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__18));
v___x_227_ = l_String_toRawSubstring_x27(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Array_mkArray0(lean_box(0));
return v___x_236_;
}
}
static lean_object* _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__27));
v___x_239_ = l_String_toRawSubstring_x27(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(lean_object* v_x_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
lean_inc(v_x_248_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_248_);
v___x_253_ = lean_box(1);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v_a_250_);
return v___x_254_;
}
else
{
lean_object* v_quotContext_255_; lean_object* v_currMacroScope_256_; lean_object* v_ref_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_elems_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_quotContext_255_ = lean_ctor_get(v_a_249_, 1);
v_currMacroScope_256_ = lean_ctor_get(v_a_249_, 2);
v_ref_257_ = lean_ctor_get(v_a_249_, 5);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = l_Lean_Syntax_getArg(v_x_248_, v___x_258_);
lean_dec(v_x_248_);
v_elems_260_ = l_Lean_Syntax_getArgs(v___x_259_);
lean_dec(v___x_259_);
v___x_261_ = 0;
v___x_262_ = l_Lean_SourceInfo_fromRef(v_ref_257_, v___x_261_);
v___x_263_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
v___x_264_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__6);
v___x_265_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__8));
lean_inc_n(v_currMacroScope_256_, 3);
lean_inc_n(v_quotContext_255_, 3);
v___x_266_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_265_, v_currMacroScope_256_);
v___x_267_ = lean_box(0);
v___x_268_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__12));
lean_inc_n(v___x_262_, 12);
v___x_269_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_269_, 0, v___x_262_);
lean_ctor_set(v___x_269_, 1, v___x_264_);
lean_ctor_set(v___x_269_, 2, v___x_266_);
lean_ctor_set(v___x_269_, 3, v___x_268_);
v___x_270_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_271_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__16));
v___x_272_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_262_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__19);
v___x_275_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__20));
v___x_276_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_275_, v_currMacroScope_256_);
v___x_277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_277_, 0, v___x_262_);
lean_ctor_set(v___x_277_, 1, v___x_274_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_ctor_set(v___x_277_, 3, v___x_267_);
v___x_278_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__21));
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_262_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_elems_260_);
v___x_281_ = lean_array_get_size(v___x_280_);
lean_dec_ref(v___x_280_);
v___x_282_ = l_Nat_reprFast(v___x_281_);
v___x_283_ = lean_box(2);
v___x_284_ = l_Lean_Syntax_mkNumLit(v___x_282_, v___x_283_);
v___x_285_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_262_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_Syntax_node5(v___x_262_, v___x_271_, v___x_273_, v___x_277_, v___x_279_, v___x_284_, v___x_286_);
v___x_288_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
v___x_289_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__25));
v___x_290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_262_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_292_ = l_Array_append___redArg(v___x_291_, v_elems_260_);
lean_dec_ref(v_elems_260_);
v___x_293_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_293_, 0, v___x_262_);
lean_ctor_set(v___x_293_, 1, v___x_270_);
lean_ctor_set(v___x_293_, 2, v___x_292_);
v___x_294_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__17));
v___x_295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_262_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = l_Lean_Syntax_node3(v___x_262_, v___x_288_, v___x_290_, v___x_293_, v___x_295_);
v___x_297_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__28);
v___x_298_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__29));
v___x_299_ = l_Lean_addMacroScope(v_quotContext_255_, v___x_298_, v_currMacroScope_256_);
v___x_300_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__31));
v___x_301_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_301_, 0, v___x_262_);
lean_ctor_set(v___x_301_, 1, v___x_297_);
lean_ctor_set(v___x_301_, 2, v___x_299_);
lean_ctor_set(v___x_301_, 3, v___x_300_);
v___x_302_ = l_Lean_Syntax_node3(v___x_262_, v___x_270_, v___x_287_, v___x_296_, v___x_301_);
v___x_303_ = l_Lean_Syntax_node2(v___x_262_, v___x_263_, v___x_269_, v___x_302_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v_a_250_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___boxed(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1(v_x_305_, v_a_306_, v_a_307_);
lean_dec_ref(v_a_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk(lean_object* v_x_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__4));
lean_inc(v_x_309_);
v___x_313_ = l_Lean_Syntax_isOfKind(v_x_309_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_x_309_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = l_Lean_Syntax_getArg(v_x_309_, v___x_316_);
lean_dec(v_x_309_);
v___x_318_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_317_);
v___x_319_ = l_Lean_Syntax_matchesNull(v___x_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v___x_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v_a_311_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = l_Lean_Syntax_getArg(v___x_317_, v___x_322_);
lean_dec(v___x_317_);
v___x_324_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__24));
lean_inc(v___x_323_);
v___x_325_ = l_Lean_Syntax_isOfKind(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_a_311_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_328_ = l_Lean_Syntax_getArg(v___x_323_, v___x_316_);
lean_dec(v___x_323_);
v___x_329_ = l_Lean_Syntax_getArgs(v___x_328_);
lean_dec(v___x_328_);
v___x_330_ = 0;
v___x_331_ = l_Lean_SourceInfo_fromRef(v_a_310_, v___x_330_);
v___x_332_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__2));
v___x_333_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__5));
lean_inc_n(v___x_331_, 3);
v___x_334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_331_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_336_ = lean_obj_once(&l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26, &l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26_once, _init_l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__26);
v___x_337_ = l_Array_append___redArg(v___x_336_, v___x_329_);
lean_dec_ref(v___x_329_);
v___x_338_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_338_, 0, v___x_331_);
lean_ctor_set(v___x_338_, 1, v___x_335_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
v___x_339_ = ((lean_object*)(l_Vector_term_x23v_x5b___x2c_x5d___closed__17));
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_331_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_Syntax_node3(v___x_331_, v___x_332_, v___x_334_, v___x_338_, v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_311_);
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unexpandMk___boxed(lean_object* v_x_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Vector_unexpandMk(v_x_343_, v_a_344_, v_a_345_);
lean_dec(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___redArg(lean_object* v_xs_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_array_to_list(v_xs_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList(lean_object* v_00_u03b1_349_, lean_object* v_n_350_, lean_object* v_xs_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_array_to_list(v_xs_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Vector_toList___boxed(lean_object* v_00_u03b1_353_, lean_object* v_n_354_, lean_object* v_xs_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Vector_toList(v_00_u03b1_353_, v_n_354_, v_xs_355_);
lean_dec(v_n_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___redArg(lean_object* v_mk_357_, lean_object* v_x_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_2(v_mk_357_, v_x_358_, lean_box(0));
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray(lean_object* v_00_u03b1_360_, lean_object* v_n_361_, lean_object* v_motive_362_, lean_object* v_mk_363_, lean_object* v_x_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_apply_2(v_mk_363_, v_x_364_, lean_box(0));
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsArray___boxed(lean_object* v_00_u03b1_366_, lean_object* v_n_367_, lean_object* v_motive_368_, lean_object* v_mk_369_, lean_object* v_x_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Vector_elimAsArray(v_00_u03b1_366_, v_n_367_, v_motive_368_, v_mk_369_, v_x_370_);
lean_dec(v_n_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___redArg(lean_object* v_mk_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_toList_374_; lean_object* v___x_375_; 
v_toList_374_ = lean_array_to_list(v_x_373_);
v___x_375_ = lean_apply_2(v_mk_372_, v_toList_374_, lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList(lean_object* v_00_u03b1_376_, lean_object* v_n_377_, lean_object* v_motive_378_, lean_object* v_mk_379_, lean_object* v_x_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Vector_elimAsList___redArg(v_mk_379_, v_x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Vector_elimAsList___boxed(lean_object* v_00_u03b1_382_, lean_object* v_n_383_, lean_object* v_motive_384_, lean_object* v_mk_385_, lean_object* v_x_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Vector_elimAsList(v_00_u03b1_382_, v_n_383_, v_motive_384_, v_mk_385_, v_x_386_);
lean_dec(v_n_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg(lean_object* v_capacity_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = lean_mk_empty_array_with_capacity(v_capacity_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Vector_emptyWithCapacity___redArg(v_capacity_390_);
lean_dec(v_capacity_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity(lean_object* v_00_u03b1_392_, lean_object* v_capacity_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = lean_mk_empty_array_with_capacity(v_capacity_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Vector_emptyWithCapacity___boxed(lean_object* v_00_u03b1_395_, lean_object* v_capacity_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Vector_emptyWithCapacity(v_00_u03b1_395_, v_capacity_396_);
lean_dec(v_capacity_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate___redArg(lean_object* v_n_398_, lean_object* v_v_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_mk_array(v_n_398_, v_v_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Vector_replicate(lean_object* v_00_u03b1_401_, lean_object* v_n_402_, lean_object* v_v_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lean_mk_array(v_n_402_, v_v_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton___redArg(lean_object* v_v_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_406_);
v___x_408_ = lean_array_push(v___x_407_, v_v_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Vector_singleton(lean_object* v_00_u03b1_409_, lean_object* v_v_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = lean_mk_empty_array_with_capacity(v___x_411_);
v___x_413_ = lean_array_push(v___x_412_, v_v_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited___redArg(lean_object* v_n_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_mk_array(v_n_414_, v_inst_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Vector_instInhabited(lean_object* v_00_u03b1_417_, lean_object* v_n_418_, lean_object* v_inst_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_mk_array(v_n_418_, v_inst_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg(lean_object* v_xs_421_, lean_object* v_i_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_array_fget_borrowed(v_xs_421_, v_i_422_);
lean_inc(v___x_423_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___redArg___boxed(lean_object* v_xs_424_, lean_object* v_i_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Vector_get___redArg(v_xs_424_, v_i_425_);
lean_dec(v_i_425_);
lean_dec_ref(v_xs_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Vector_get(lean_object* v_00_u03b1_427_, lean_object* v_n_428_, lean_object* v_xs_429_, lean_object* v_i_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_array_fget_borrowed(v_xs_429_, v_i_430_);
lean_inc(v___x_431_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Vector_get___boxed(lean_object* v_00_u03b1_432_, lean_object* v_n_433_, lean_object* v_xs_434_, lean_object* v_i_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Vector_get(v_00_u03b1_432_, v_n_433_, v_xs_434_, v_i_435_);
lean_dec(v_i_435_);
lean_dec_ref(v_xs_434_);
lean_dec(v_n_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg(lean_object* v_xs_437_, size_t v_i_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = lean_array_uget_borrowed(v_xs_437_, v_i_438_);
lean_inc(v___x_439_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___redArg___boxed(lean_object* v_xs_440_, lean_object* v_i_441_){
_start:
{
size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_res_443_ = l_Vector_uget___redArg(v_xs_440_, v_i_boxed_442_);
lean_dec_ref(v_xs_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget(lean_object* v_00_u03b1_444_, lean_object* v_n_445_, lean_object* v_xs_446_, size_t v_i_447_, lean_object* v_h_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = lean_array_uget_borrowed(v_xs_446_, v_i_447_);
lean_inc(v___x_449_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Vector_uget___boxed(lean_object* v_00_u03b1_450_, lean_object* v_n_451_, lean_object* v_xs_452_, lean_object* v_i_453_, lean_object* v_h_454_){
_start:
{
size_t v_i_boxed_455_; lean_object* v_res_456_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_453_);
lean_dec(v_i_453_);
v_res_456_ = l_Vector_uget(v_00_u03b1_450_, v_n_451_, v_xs_452_, v_i_boxed_455_, v_h_454_);
lean_dec_ref(v_xs_452_);
lean_dec(v_n_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0(lean_object* v_xs_457_, lean_object* v_i_458_, lean_object* v_h_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_array_fget_borrowed(v_xs_457_, v_i_458_);
lean_inc(v___x_460_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___lam__0___boxed(lean_object* v_xs_461_, lean_object* v_i_462_, lean_object* v_h_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Vector_instGetElemNatLt___lam__0(v_xs_461_, v_i_462_, v_h_463_);
lean_dec(v_i_462_);
lean_dec_ref(v_xs_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt(lean_object* v_00_u03b1_466_, lean_object* v_n_467_){
_start:
{
lean_object* v___f_468_; 
v___f_468_ = ((lean_object*)(l_Vector_instGetElemNatLt___closed__0));
return v___f_468_;
}
}
LEAN_EXPORT lean_object* l_Vector_instGetElemNatLt___boxed(lean_object* v_00_u03b1_469_, lean_object* v_n_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Vector_instGetElemNatLt(v_00_u03b1_469_, v_n_470_);
lean_dec(v_n_470_);
return v_res_471_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains___redArg(lean_object* v_inst_472_, lean_object* v_xs_473_, lean_object* v_a_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = l_Array_contains___redArg(v_inst_472_, v_xs_473_, v_a_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___redArg___boxed(lean_object* v_inst_476_, lean_object* v_xs_477_, lean_object* v_a_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Vector_contains___redArg(v_inst_476_, v_xs_477_, v_a_478_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT uint8_t l_Vector_contains(lean_object* v_00_u03b1_481_, lean_object* v_n_482_, lean_object* v_inst_483_, lean_object* v_xs_484_, lean_object* v_a_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Array_contains___redArg(v_inst_483_, v_xs_484_, v_a_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Vector_contains___boxed(lean_object* v_00_u03b1_487_, lean_object* v_n_488_, lean_object* v_inst_489_, lean_object* v_xs_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Vector_contains(v_00_u03b1_487_, v_n_488_, v_inst_489_, v_xs_490_, v_a_491_);
lean_dec(v_n_488_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership(lean_object* v_00_u03b1_494_, lean_object* v_n_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = lean_box(0);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Vector_instMembership___boxed(lean_object* v_00_u03b1_497_, lean_object* v_n_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Vector_instMembership(v_00_u03b1_497_, v_n_498_);
lean_dec(v_n_498_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg(lean_object* v_xs_500_, lean_object* v_i_501_, lean_object* v_default_502_){
_start:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_get_size(v_xs_500_);
v___x_504_ = lean_nat_dec_lt(v_i_501_, v___x_503_);
if (v___x_504_ == 0)
{
lean_inc(v_default_502_);
return v_default_502_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = lean_array_fget_borrowed(v_xs_500_, v_i_501_);
lean_inc(v___x_505_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___redArg___boxed(lean_object* v_xs_506_, lean_object* v_i_507_, lean_object* v_default_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Vector_getD___redArg(v_xs_506_, v_i_507_, v_default_508_);
lean_dec(v_default_508_);
lean_dec(v_i_507_);
lean_dec_ref(v_xs_506_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Vector_getD(lean_object* v_00_u03b1_510_, lean_object* v_n_511_, lean_object* v_xs_512_, lean_object* v_i_513_, lean_object* v_default_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_xs_512_);
v___x_516_ = lean_nat_dec_lt(v_i_513_, v___x_515_);
if (v___x_516_ == 0)
{
lean_inc(v_default_514_);
return v_default_514_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = lean_array_fget_borrowed(v_xs_512_, v_i_513_);
lean_inc(v___x_517_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_getD___boxed(lean_object* v_00_u03b1_518_, lean_object* v_n_519_, lean_object* v_xs_520_, lean_object* v_i_521_, lean_object* v_default_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Vector_getD(v_00_u03b1_518_, v_n_519_, v_xs_520_, v_i_521_, v_default_522_);
lean_dec(v_default_522_);
lean_dec(v_i_521_);
lean_dec_ref(v_xs_520_);
lean_dec(v_n_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg(lean_object* v_inst_524_, lean_object* v_xs_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_array_get_size(v_xs_525_);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_array_get_borrowed(v_inst_524_, v_xs_525_, v___x_528_);
lean_dec(v___x_528_);
lean_inc(v___x_529_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___redArg___boxed(lean_object* v_inst_530_, lean_object* v_xs_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Vector_back_x21___redArg(v_inst_530_, v_xs_531_);
lean_dec_ref(v_xs_531_);
lean_dec(v_inst_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21(lean_object* v_00_u03b1_533_, lean_object* v_n_534_, lean_object* v_inst_535_, lean_object* v_xs_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_537_ = lean_array_get_size(v_xs_536_);
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_sub(v___x_537_, v___x_538_);
v___x_540_ = lean_array_get_borrowed(v_inst_535_, v_xs_536_, v___x_539_);
lean_dec(v___x_539_);
lean_inc(v___x_540_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x21___boxed(lean_object* v_00_u03b1_541_, lean_object* v_n_542_, lean_object* v_inst_543_, lean_object* v_xs_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Vector_back_x21(v_00_u03b1_541_, v_n_542_, v_inst_543_, v_xs_544_);
lean_dec_ref(v_xs_544_);
lean_dec(v_inst_543_);
lean_dec(v_n_542_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg(lean_object* v_xs_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_array_get_size(v_xs_546_);
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_sub(v___x_547_, v___x_548_);
v___x_550_ = lean_nat_dec_lt(v___x_549_, v___x_547_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec(v___x_549_);
v___x_551_ = lean_box(0);
return v___x_551_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_array_fget_borrowed(v_xs_546_, v___x_549_);
lean_dec(v___x_549_);
lean_inc(v___x_552_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___redArg___boxed(lean_object* v_xs_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Vector_back_x3f___redArg(v_xs_554_);
lean_dec_ref(v_xs_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f(lean_object* v_00_u03b1_556_, lean_object* v_n_557_, lean_object* v_xs_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = lean_array_get_size(v_xs_558_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_sub(v___x_559_, v___x_560_);
v___x_562_ = lean_nat_dec_lt(v___x_561_, v___x_559_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_561_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_array_fget_borrowed(v_xs_558_, v___x_561_);
lean_dec(v___x_561_);
lean_inc(v___x_564_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_back_x3f___boxed(lean_object* v_00_u03b1_566_, lean_object* v_n_567_, lean_object* v_xs_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Vector_back_x3f(v_00_u03b1_566_, v_n_567_, v_xs_568_);
lean_dec_ref(v_xs_568_);
lean_dec(v_n_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg(lean_object* v_n_570_, lean_object* v_xs_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_sub(v_n_570_, v___x_572_);
v___x_574_ = lean_array_fget_borrowed(v_xs_571_, v___x_573_);
lean_dec(v___x_573_);
lean_inc(v___x_574_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___redArg___boxed(lean_object* v_n_575_, lean_object* v_xs_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Vector_back___redArg(v_n_575_, v_xs_576_);
lean_dec_ref(v_xs_576_);
lean_dec(v_n_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Vector_back(lean_object* v_n_578_, lean_object* v_00_u03b1_579_, lean_object* v_inst_580_, lean_object* v_xs_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_sub(v_n_578_, v___x_582_);
v___x_584_ = lean_array_fget_borrowed(v_xs_581_, v___x_583_);
lean_dec(v___x_583_);
lean_inc(v___x_584_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Vector_back___boxed(lean_object* v_n_585_, lean_object* v_00_u03b1_586_, lean_object* v_inst_587_, lean_object* v_xs_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Vector_back(v_n_585_, v_00_u03b1_586_, v_inst_587_, v_xs_588_);
lean_dec_ref(v_xs_588_);
lean_dec(v_n_585_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg(lean_object* v_xs_590_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_array_fget_borrowed(v_xs_590_, v___x_591_);
lean_inc(v___x_592_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___redArg___boxed(lean_object* v_xs_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Vector_head___redArg(v_xs_593_);
lean_dec_ref(v_xs_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Vector_head(lean_object* v_n_595_, lean_object* v_00_u03b1_596_, lean_object* v_inst_597_, lean_object* v_xs_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_fget_borrowed(v_xs_598_, v___x_599_);
lean_inc(v___x_600_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Vector_head___boxed(lean_object* v_n_601_, lean_object* v_00_u03b1_602_, lean_object* v_inst_603_, lean_object* v_xs_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Vector_head(v_n_601_, v_00_u03b1_602_, v_inst_603_, v_xs_604_);
lean_dec_ref(v_xs_604_);
lean_dec(v_n_601_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___redArg(lean_object* v_xs_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_array_push(v_xs_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Vector_push(lean_object* v_00_u03b1_609_, lean_object* v_n_610_, lean_object* v_xs_611_, lean_object* v_x_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = lean_array_push(v_xs_611_, v_x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Vector_push___boxed(lean_object* v_00_u03b1_614_, lean_object* v_n_615_, lean_object* v_xs_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Vector_push(v_00_u03b1_614_, v_n_615_, v_xs_616_, v_x_617_);
lean_dec(v_n_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___redArg(lean_object* v_xs_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = lean_array_pop(v_xs_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop(lean_object* v_00_u03b1_621_, lean_object* v_n_622_, lean_object* v_xs_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_pop(v_xs_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Vector_pop___boxed(lean_object* v_00_u03b1_625_, lean_object* v_n_626_, lean_object* v_xs_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Vector_pop(v_00_u03b1_625_, v_n_626_, v_xs_627_);
lean_dec(v_n_626_);
return v_res_628_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__9(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Vector_set___auto__1___closed__8));
v___x_649_ = l_Lean_mkAtom(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__10(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_obj_once(&l_Vector_set___auto__1___closed__9, &l_Vector_set___auto__1___closed__9_once, _init_l_Vector_set___auto__1___closed__9);
v___x_651_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_652_ = lean_array_push(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__11(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_obj_once(&l_Vector_set___auto__1___closed__10, &l_Vector_set___auto__1___closed__10_once, _init_l_Vector_set___auto__1___closed__10);
v___x_654_ = ((lean_object*)(l_Vector_set___auto__1___closed__7));
v___x_655_ = lean_box(2);
v___x_656_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
lean_ctor_set(v___x_656_, 2, v___x_653_);
return v___x_656_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__12(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_obj_once(&l_Vector_set___auto__1___closed__11, &l_Vector_set___auto__1___closed__11_once, _init_l_Vector_set___auto__1___closed__11);
v___x_658_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_659_ = lean_array_push(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__13(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_660_ = lean_obj_once(&l_Vector_set___auto__1___closed__12, &l_Vector_set___auto__1___closed__12_once, _init_l_Vector_set___auto__1___closed__12);
v___x_661_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_662_ = lean_box(2);
v___x_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_661_);
lean_ctor_set(v___x_663_, 2, v___x_660_);
return v___x_663_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__14(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_obj_once(&l_Vector_set___auto__1___closed__13, &l_Vector_set___auto__1___closed__13_once, _init_l_Vector_set___auto__1___closed__13);
v___x_665_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_666_ = lean_array_push(v___x_665_, v___x_664_);
return v___x_666_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__15(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_667_ = lean_obj_once(&l_Vector_set___auto__1___closed__14, &l_Vector_set___auto__1___closed__14_once, _init_l_Vector_set___auto__1___closed__14);
v___x_668_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_669_ = lean_box(2);
v___x_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
lean_ctor_set(v___x_670_, 2, v___x_667_);
return v___x_670_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__16(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l_Vector_set___auto__1___closed__15, &l_Vector_set___auto__1___closed__15_once, _init_l_Vector_set___auto__1___closed__15);
v___x_672_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_673_ = lean_array_push(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Vector_set___auto__1___closed__17(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = lean_obj_once(&l_Vector_set___auto__1___closed__16, &l_Vector_set___auto__1___closed__16_once, _init_l_Vector_set___auto__1___closed__16);
v___x_675_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_676_ = lean_box(2);
v___x_677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_674_);
return v___x_677_;
}
}
static lean_object* _init_l_Vector_set___auto__1(void){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg(lean_object* v_xs_679_, lean_object* v_i_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_array_fset(v_xs_679_, v_i_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___redArg___boxed(lean_object* v_xs_683_, lean_object* v_i_684_, lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Vector_set___redArg(v_xs_683_, v_i_684_, v_x_685_);
lean_dec(v_i_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Vector_set(lean_object* v_00_u03b1_687_, lean_object* v_n_688_, lean_object* v_xs_689_, lean_object* v_i_690_, lean_object* v_x_691_, lean_object* v_h_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_array_fset(v_xs_689_, v_i_690_, v_x_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Vector_set___boxed(lean_object* v_00_u03b1_694_, lean_object* v_n_695_, lean_object* v_xs_696_, lean_object* v_i_697_, lean_object* v_x_698_, lean_object* v_h_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Vector_set(v_00_u03b1_694_, v_n_695_, v_xs_696_, v_i_697_, v_x_698_, v_h_699_);
lean_dec(v_i_697_);
lean_dec(v_n_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg(lean_object* v_xs_701_, lean_object* v_i_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_array_get_size(v_xs_701_);
v___x_705_ = lean_nat_dec_lt(v_i_702_, v___x_704_);
if (v___x_705_ == 0)
{
lean_dec(v_x_703_);
return v_xs_701_;
}
else
{
lean_object* v___x_706_; 
v___x_706_ = lean_array_fset(v_xs_701_, v_i_702_, v_x_703_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___redArg___boxed(lean_object* v_xs_707_, lean_object* v_i_708_, lean_object* v_x_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Vector_setIfInBounds___redArg(v_xs_707_, v_i_708_, v_x_709_);
lean_dec(v_i_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds(lean_object* v_00_u03b1_711_, lean_object* v_n_712_, lean_object* v_xs_713_, lean_object* v_i_714_, lean_object* v_x_715_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_array_get_size(v_xs_713_);
v___x_717_ = lean_nat_dec_lt(v_i_714_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec(v_x_715_);
return v_xs_713_;
}
else
{
lean_object* v___x_718_; 
v___x_718_ = lean_array_fset(v_xs_713_, v_i_714_, v_x_715_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_setIfInBounds___boxed(lean_object* v_00_u03b1_719_, lean_object* v_n_720_, lean_object* v_xs_721_, lean_object* v_i_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Vector_setIfInBounds(v_00_u03b1_719_, v_n_720_, v_xs_721_, v_i_722_, v_x_723_);
lean_dec(v_i_722_);
lean_dec(v_n_720_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg(lean_object* v_xs_725_, lean_object* v_i_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_array_set(v_xs_725_, v_i_726_, v_x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___redArg___boxed(lean_object* v_xs_729_, lean_object* v_i_730_, lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Vector_set_x21___redArg(v_xs_729_, v_i_730_, v_x_731_);
lean_dec(v_i_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21(lean_object* v_00_u03b1_733_, lean_object* v_n_734_, lean_object* v_xs_735_, lean_object* v_i_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_array_set(v_xs_735_, v_i_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Vector_set_x21___boxed(lean_object* v_00_u03b1_739_, lean_object* v_n_740_, lean_object* v_xs_741_, lean_object* v_i_742_, lean_object* v_x_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Vector_set_x21(v_00_u03b1_739_, v_n_740_, v_xs_741_, v_i_742_, v_x_743_);
lean_dec(v_i_742_);
lean_dec(v_n_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___redArg(lean_object* v_inst_745_, lean_object* v_f_746_, lean_object* v_b_747_, lean_object* v_xs_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_xs_748_);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v_toApplicative_752_; lean_object* v_toPure_753_; lean_object* v___x_754_; 
lean_dec_ref(v_xs_748_);
lean_dec(v_f_746_);
v_toApplicative_752_ = lean_ctor_get(v_inst_745_, 0);
lean_inc_ref(v_toApplicative_752_);
lean_dec_ref(v_inst_745_);
v_toPure_753_ = lean_ctor_get(v_toApplicative_752_, 1);
lean_inc(v_toPure_753_);
lean_dec_ref(v_toApplicative_752_);
v___x_754_ = lean_apply_2(v_toPure_753_, lean_box(0), v_b_747_);
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_le(v___x_750_, v___x_750_);
if (v___x_755_ == 0)
{
if (v___x_751_ == 0)
{
lean_object* v_toApplicative_756_; lean_object* v_toPure_757_; lean_object* v___x_758_; 
lean_dec_ref(v_xs_748_);
lean_dec(v_f_746_);
v_toApplicative_756_ = lean_ctor_get(v_inst_745_, 0);
lean_inc_ref(v_toApplicative_756_);
lean_dec_ref(v_inst_745_);
v_toPure_757_ = lean_ctor_get(v_toApplicative_756_, 1);
lean_inc(v_toPure_757_);
lean_dec_ref(v_toApplicative_756_);
v___x_758_ = lean_apply_2(v_toPure_757_, lean_box(0), v_b_747_);
return v___x_758_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_750_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v_f_746_, v_xs_748_, v___x_759_, v___x_760_, v_b_747_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_750_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v_f_746_, v_xs_748_, v___x_762_, v___x_763_, v_b_747_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_765_, lean_object* v_00_u03b2_766_, lean_object* v_00_u03b1_767_, lean_object* v_n_768_, lean_object* v_inst_769_, lean_object* v_f_770_, lean_object* v_b_771_, lean_object* v_xs_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_xs_772_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_776_; lean_object* v_toPure_777_; lean_object* v___x_778_; 
lean_dec_ref(v_xs_772_);
lean_dec(v_f_770_);
v_toApplicative_776_ = lean_ctor_get(v_inst_769_, 0);
lean_inc_ref(v_toApplicative_776_);
lean_dec_ref(v_inst_769_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_776_);
v___x_778_ = lean_apply_2(v_toPure_777_, lean_box(0), v_b_771_);
return v___x_778_;
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_779_ == 0)
{
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_780_; lean_object* v_toPure_781_; lean_object* v___x_782_; 
lean_dec_ref(v_xs_772_);
lean_dec(v_f_770_);
v_toApplicative_780_ = lean_ctor_get(v_inst_769_, 0);
lean_inc_ref(v_toApplicative_780_);
lean_dec_ref(v_inst_769_);
v_toPure_781_ = lean_ctor_get(v_toApplicative_780_, 1);
lean_inc(v_toPure_781_);
lean_dec_ref(v_toApplicative_780_);
v___x_782_ = lean_apply_2(v_toPure_781_, lean_box(0), v_b_771_);
return v___x_782_;
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_774_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_769_, v_f_770_, v_xs_772_, v___x_783_, v___x_784_, v_b_771_);
return v___x_785_;
}
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_of_nat(v___x_774_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_769_, v_f_770_, v_xs_772_, v___x_786_, v___x_787_, v_b_771_);
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_789_, lean_object* v_00_u03b2_790_, lean_object* v_00_u03b1_791_, lean_object* v_n_792_, lean_object* v_inst_793_, lean_object* v_f_794_, lean_object* v_b_795_, lean_object* v_xs_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Vector_foldlM(v_m_789_, v_00_u03b2_790_, v_00_u03b1_791_, v_n_792_, v_inst_793_, v_f_794_, v_b_795_, v_xs_796_);
lean_dec(v_n_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_798_, lean_object* v_f_799_, lean_object* v_b_800_, lean_object* v_xs_801_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_array_get_size(v_xs_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_nat_dec_lt(v___x_803_, v___x_802_);
if (v___x_804_ == 0)
{
lean_object* v_toApplicative_805_; lean_object* v_toPure_806_; lean_object* v___x_807_; 
lean_dec_ref(v_xs_801_);
lean_dec(v_f_799_);
v_toApplicative_805_ = lean_ctor_get(v_inst_798_, 0);
lean_inc_ref(v_toApplicative_805_);
lean_dec_ref(v_inst_798_);
v_toPure_806_ = lean_ctor_get(v_toApplicative_805_, 1);
lean_inc(v_toPure_806_);
lean_dec_ref(v_toApplicative_805_);
v___x_807_ = lean_apply_2(v_toPure_806_, lean_box(0), v_b_800_);
return v___x_807_;
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_usize_of_nat(v___x_802_);
v___x_809_ = ((size_t)0ULL);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_798_, v_f_799_, v_xs_801_, v___x_808_, v___x_809_, v_b_800_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_811_, lean_object* v_00_u03b1_812_, lean_object* v_00_u03b2_813_, lean_object* v_n_814_, lean_object* v_inst_815_, lean_object* v_f_816_, lean_object* v_b_817_, lean_object* v_xs_818_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_array_get_size(v_xs_818_);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_nat_dec_lt(v___x_820_, v___x_819_);
if (v___x_821_ == 0)
{
lean_object* v_toApplicative_822_; lean_object* v_toPure_823_; lean_object* v___x_824_; 
lean_dec_ref(v_xs_818_);
lean_dec(v_f_816_);
v_toApplicative_822_ = lean_ctor_get(v_inst_815_, 0);
lean_inc_ref(v_toApplicative_822_);
lean_dec_ref(v_inst_815_);
v_toPure_823_ = lean_ctor_get(v_toApplicative_822_, 1);
lean_inc(v_toPure_823_);
lean_dec_ref(v_toApplicative_822_);
v___x_824_ = lean_apply_2(v_toPure_823_, lean_box(0), v_b_817_);
return v___x_824_;
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_usize_of_nat(v___x_819_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_815_, v_f_816_, v_xs_818_, v___x_825_, v___x_826_, v_b_817_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_828_, lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_n_831_, lean_object* v_inst_832_, lean_object* v_f_833_, lean_object* v_b_834_, lean_object* v_xs_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Vector_foldrM(v_m_828_, v_00_u03b1_829_, v_00_u03b2_830_, v_n_831_, v_inst_832_, v_f_833_, v_b_834_, v_xs_835_);
lean_dec(v_n_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_837_, lean_object* v_x1_838_, lean_object* v_x2_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_apply_2(v_f_837_, v_x1_838_, v_x2_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_860_, lean_object* v_b_861_, lean_object* v_xs_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_array_get_size(v_xs_862_);
v___x_865_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_866_ = lean_nat_dec_lt(v___x_863_, v___x_864_);
if (v___x_866_ == 0)
{
lean_dec_ref(v_xs_862_);
lean_dec(v_f_860_);
return v_b_861_;
}
else
{
lean_object* v___f_867_; uint8_t v___x_868_; 
v___f_867_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_867_, 0, v_f_860_);
v___x_868_ = lean_nat_dec_le(v___x_864_, v___x_864_);
if (v___x_868_ == 0)
{
if (v___x_866_ == 0)
{
lean_dec_ref(v___f_867_);
lean_dec_ref(v_xs_862_);
return v_b_861_;
}
else
{
size_t v___x_869_; size_t v___x_870_; lean_object* v___x_871_; 
v___x_869_ = ((size_t)0ULL);
v___x_870_ = lean_usize_of_nat(v___x_864_);
v___x_871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_867_, v_xs_862_, v___x_869_, v___x_870_, v_b_861_);
return v___x_871_;
}
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_usize_of_nat(v___x_864_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_865_, v___f_867_, v_xs_862_, v___x_872_, v___x_873_, v_b_861_);
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_875_, lean_object* v_00_u03b1_876_, lean_object* v_n_877_, lean_object* v_f_878_, lean_object* v_b_879_, lean_object* v_xs_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_array_get_size(v_xs_880_);
v___x_883_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_884_ = lean_nat_dec_lt(v___x_881_, v___x_882_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_xs_880_);
lean_dec(v_f_878_);
return v_b_879_;
}
else
{
lean_object* v___f_885_; uint8_t v___x_886_; 
v___f_885_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_885_, 0, v_f_878_);
v___x_886_ = lean_nat_dec_le(v___x_882_, v___x_882_);
if (v___x_886_ == 0)
{
if (v___x_884_ == 0)
{
lean_dec_ref(v___f_885_);
lean_dec_ref(v_xs_880_);
return v_b_879_;
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_882_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_883_, v___f_885_, v_xs_880_, v___x_887_, v___x_888_, v_b_879_);
return v___x_889_;
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_882_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_883_, v___f_885_, v_xs_880_, v___x_890_, v___x_891_, v_b_879_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_893_, lean_object* v_00_u03b1_894_, lean_object* v_n_895_, lean_object* v_f_896_, lean_object* v_b_897_, lean_object* v_xs_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Vector_foldl(v_00_u03b2_893_, v_00_u03b1_894_, v_n_895_, v_f_896_, v_b_897_, v_xs_898_);
lean_dec(v_n_895_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_900_, lean_object* v_b_901_, lean_object* v_xs_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_903_ = lean_array_get_size(v_xs_902_);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_906_ = lean_nat_dec_lt(v___x_904_, v___x_903_);
if (v___x_906_ == 0)
{
lean_dec_ref(v_xs_902_);
lean_dec(v_f_900_);
return v_b_901_;
}
else
{
lean_object* v___f_907_; size_t v___x_908_; size_t v___x_909_; lean_object* v___x_910_; 
v___f_907_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_907_, 0, v_f_900_);
v___x_908_ = lean_usize_of_nat(v___x_903_);
v___x_909_ = ((size_t)0ULL);
v___x_910_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_905_, v___f_907_, v_xs_902_, v___x_908_, v___x_909_, v_b_901_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_911_, lean_object* v_00_u03b2_912_, lean_object* v_n_913_, lean_object* v_f_914_, lean_object* v_b_915_, lean_object* v_xs_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_917_ = lean_array_get_size(v_xs_916_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_917_);
if (v___x_920_ == 0)
{
lean_dec_ref(v_xs_916_);
lean_dec(v_f_914_);
return v_b_915_;
}
else
{
lean_object* v___f_921_; size_t v___x_922_; size_t v___x_923_; lean_object* v___x_924_; 
v___f_921_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_921_, 0, v_f_914_);
v___x_922_ = lean_usize_of_nat(v___x_917_);
v___x_923_ = ((size_t)0ULL);
v___x_924_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_919_, v___f_921_, v_xs_916_, v___x_922_, v___x_923_, v_b_915_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_n_927_, lean_object* v_f_928_, lean_object* v_b_929_, lean_object* v_xs_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Vector_foldr(v_00_u03b1_925_, v_00_u03b2_926_, v_n_927_, v_f_928_, v_b_929_, v_xs_930_);
lean_dec(v_n_927_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_932_, lean_object* v_ys_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Array_append___redArg(v_xs_932_, v_ys_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_935_, lean_object* v_ys_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Vector_append___redArg(v_xs_935_, v_ys_936_);
lean_dec_ref(v_ys_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_938_, lean_object* v_n_939_, lean_object* v_m_940_, lean_object* v_xs_941_, lean_object* v_ys_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Array_append___redArg(v_xs_941_, v_ys_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_944_, lean_object* v_n_945_, lean_object* v_m_946_, lean_object* v_xs_947_, lean_object* v_ys_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Vector_append(v_00_u03b1_944_, v_n_945_, v_m_946_, v_xs_947_, v_ys_948_);
lean_dec_ref(v_ys_948_);
lean_dec(v_m_946_);
lean_dec(v_n_945_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_950_, lean_object* v_m_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_952_, 0, lean_box(0));
lean_closure_set(v___x_952_, 1, v_n_950_);
lean_closure_set(v___x_952_, 2, v_m_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_953_, lean_object* v_n_954_, lean_object* v_m_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_956_, 0, lean_box(0));
lean_closure_set(v___x_956_, 1, v_n_954_);
lean_closure_set(v___x_956_, 2, v_m_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_957_){
_start:
{
lean_inc_ref(v_xs_957_);
return v_xs_957_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Vector_cast___redArg(v_xs_958_);
lean_dec_ref(v_xs_958_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_960_, lean_object* v_m_961_, lean_object* v_00_u03b1_962_, lean_object* v_h_963_, lean_object* v_xs_964_){
_start:
{
lean_inc_ref(v_xs_964_);
return v_xs_964_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_965_, lean_object* v_m_966_, lean_object* v_00_u03b1_967_, lean_object* v_h_968_, lean_object* v_xs_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Vector_cast(v_n_965_, v_m_966_, v_00_u03b1_967_, v_h_968_, v_xs_969_);
lean_dec_ref(v_xs_969_);
lean_dec(v_m_966_);
lean_dec(v_n_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_971_, lean_object* v_start_972_, lean_object* v_stop_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Array_extract___redArg(v_xs_971_, v_start_972_, v_stop_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_975_, lean_object* v_start_976_, lean_object* v_stop_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Vector_extract___redArg(v_xs_975_, v_start_976_, v_stop_977_);
lean_dec_ref(v_xs_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_979_, lean_object* v_n_980_, lean_object* v_xs_981_, lean_object* v_start_982_, lean_object* v_stop_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Array_extract___redArg(v_xs_981_, v_start_982_, v_stop_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_985_, lean_object* v_n_986_, lean_object* v_xs_987_, lean_object* v_start_988_, lean_object* v_stop_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Vector_extract(v_00_u03b1_985_, v_n_986_, v_xs_987_, v_start_988_, v_stop_989_);
lean_dec_ref(v_xs_987_);
lean_dec(v_n_986_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_991_, lean_object* v_xs_992_, lean_object* v_i_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = l_Array_extract___redArg(v_xs_992_, v___x_994_, v_i_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_996_, lean_object* v_xs_997_, lean_object* v_i_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Vector_take___redArg(v_n_996_, v_xs_997_, v_i_998_);
lean_dec_ref(v_xs_997_);
lean_dec(v_n_996_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_1000_, lean_object* v_n_1001_, lean_object* v_xs_1002_, lean_object* v_i_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = l_Array_extract___redArg(v_xs_1002_, v___x_1004_, v_i_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_n_1007_, lean_object* v_xs_1008_, lean_object* v_i_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Vector_take(v_00_u03b1_1006_, v_n_1007_, v_xs_1008_, v_i_1009_);
lean_dec_ref(v_xs_1008_);
lean_dec(v_n_1007_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1011_, lean_object* v_i_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_array_get_size(v_xs_1011_);
v___x_1014_ = l_Array_extract___redArg(v_xs_1011_, v_i_1012_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1015_, lean_object* v_i_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Vector_drop___redArg(v_xs_1015_, v_i_1016_);
lean_dec_ref(v_xs_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1018_, lean_object* v_n_1019_, lean_object* v_xs_1020_, lean_object* v_i_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_array_get_size(v_xs_1020_);
v___x_1023_ = l_Array_extract___redArg(v_xs_1020_, v_i_1021_, v___x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_n_1025_, lean_object* v_xs_1026_, lean_object* v_i_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Vector_drop(v_00_u03b1_1024_, v_n_1025_, v_xs_1026_, v_i_1027_);
lean_dec_ref(v_xs_1026_);
lean_dec(v_n_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1029_, lean_object* v_i_1030_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Array_shrink___redArg(v_xs_1029_, v_i_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1032_, lean_object* v_i_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Vector_shrink___redArg(v_xs_1032_, v_i_1033_);
lean_dec(v_i_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1035_, lean_object* v_n_1036_, lean_object* v_xs_1037_, lean_object* v_i_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Array_shrink___redArg(v_xs_1037_, v_i_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_n_1041_, lean_object* v_xs_1042_, lean_object* v_i_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Vector_shrink(v_00_u03b1_1040_, v_n_1041_, v_xs_1042_, v_i_1043_);
lean_dec(v_i_1043_);
lean_dec(v_n_1041_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_apply_1(v_f_1045_, v_x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1048_, lean_object* v_xs_1049_){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; size_t v_sz_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___f_1050_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1050_, 0, v_f_1048_);
v___x_1051_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1052_ = lean_array_size(v_xs_1049_);
v___x_1053_ = ((size_t)0ULL);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1051_, v___f_1050_, v_sz_1052_, v___x_1053_, v_xs_1049_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_n_1057_, lean_object* v_f_1058_, lean_object* v_xs_1059_){
_start:
{
lean_object* v___f_1060_; lean_object* v___x_1061_; size_t v_sz_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___f_1060_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1060_, 0, v_f_1058_);
v___x_1061_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1062_ = lean_array_size(v_xs_1059_);
v___x_1063_ = ((size_t)0ULL);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1061_, v___f_1060_, v_sz_1062_, v___x_1063_, v_xs_1059_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_n_1067_, lean_object* v_f_1068_, lean_object* v_xs_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Vector_map(v_00_u03b1_1065_, v_00_u03b2_1066_, v_n_1067_, v_f_1068_, v_xs_1069_);
lean_dec(v_n_1067_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1071_, lean_object* v_i_1072_, lean_object* v_a_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_apply_2(v_f_1071_, v_i_1072_, v_a_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1076_, lean_object* v_xs_1077_){
_start:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___f_1078_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1078_, 0, v_f_1076_);
v___x_1079_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1080_ = lean_array_get_size(v_xs_1077_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_mk_empty_array_with_capacity(v___x_1080_);
v___x_1083_ = l_Array_mapFinIdxM_map___redArg(v___x_1079_, v_xs_1077_, v___f_1078_, v___x_1080_, v___x_1081_, v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_n_1086_, lean_object* v_f_1087_, lean_object* v_xs_1088_){
_start:
{
lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___f_1089_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1089_, 0, v_f_1087_);
v___x_1090_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1091_ = lean_array_get_size(v_xs_1088_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_mk_empty_array_with_capacity(v___x_1091_);
v___x_1094_ = l_Array_mapFinIdxM_map___redArg(v___x_1090_, v_xs_1088_, v___f_1089_, v___x_1091_, v___x_1092_, v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_n_1097_, lean_object* v_f_1098_, lean_object* v_xs_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Vector_mapIdx(v_00_u03b1_1095_, v_00_u03b2_1096_, v_n_1097_, v_f_1098_, v_xs_1099_);
lean_dec(v_n_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1101_, lean_object* v_x1_1102_, lean_object* v_x2_1103_, lean_object* v_x3_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_3(v_f_1101_, v_x1_1102_, v_x2_1103_, lean_box(0));
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1106_, lean_object* v_f_1107_){
_start:
{
lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___f_1108_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1108_, 0, v_f_1107_);
v___x_1109_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1110_ = lean_array_get_size(v_xs_1106_);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_mk_empty_array_with_capacity(v___x_1110_);
v___x_1113_ = l_Array_mapFinIdxM_map___redArg(v___x_1109_, v_xs_1106_, v___f_1108_, v___x_1110_, v___x_1111_, v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1114_, lean_object* v_n_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_xs_1117_, lean_object* v_f_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___f_1119_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1119_, 0, v_f_1118_);
v___x_1120_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1121_ = lean_array_get_size(v_xs_1117_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_mk_empty_array_with_capacity(v___x_1121_);
v___x_1124_ = l_Array_mapFinIdxM_map___redArg(v___x_1120_, v_xs_1117_, v___f_1119_, v___x_1121_, v___x_1122_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_n_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_xs_1128_, lean_object* v_f_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Vector_mapFinIdx(v_00_u03b1_1125_, v_n_1126_, v_00_u03b2_1127_, v_xs_1128_, v_f_1129_);
lean_dec(v_n_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1131_, lean_object* v_acc_1132_, lean_object* v_n_1133_, lean_object* v_inst_1134_, lean_object* v_f_1135_, lean_object* v_xs_1136_, lean_object* v_____do__lift_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1131_, v_acc_1132_, v_n_1133_, v_inst_1134_, v_f_1135_, v_xs_1136_, v_____do__lift_1137_);
lean_dec(v_k_1131_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1139_, lean_object* v_inst_1140_, lean_object* v_f_1141_, lean_object* v_xs_1142_, lean_object* v_k_1143_, lean_object* v_acc_1144_){
_start:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_lt(v_k_1143_, v_n_1139_);
if (v___x_1145_ == 0)
{
lean_object* v_toApplicative_1146_; lean_object* v_toPure_1147_; lean_object* v___x_1148_; 
lean_dec(v_k_1143_);
lean_dec_ref(v_xs_1142_);
lean_dec(v_f_1141_);
lean_dec(v_n_1139_);
v_toApplicative_1146_ = lean_ctor_get(v_inst_1140_, 0);
lean_inc_ref(v_toApplicative_1146_);
lean_dec_ref(v_inst_1140_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1146_, 1);
lean_inc(v_toPure_1147_);
lean_dec_ref(v_toApplicative_1146_);
v___x_1148_ = lean_apply_2(v_toPure_1147_, lean_box(0), v_acc_1144_);
return v___x_1148_;
}
else
{
lean_object* v_toBind_1149_; lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_toBind_1149_ = lean_ctor_get(v_inst_1140_, 1);
lean_inc(v_toBind_1149_);
lean_inc_ref(v_xs_1142_);
lean_inc(v_f_1141_);
lean_inc(v_k_1143_);
v___f_1150_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1150_, 0, v_k_1143_);
lean_closure_set(v___f_1150_, 1, v_acc_1144_);
lean_closure_set(v___f_1150_, 2, v_n_1139_);
lean_closure_set(v___f_1150_, 3, v_inst_1140_);
lean_closure_set(v___f_1150_, 4, v_f_1141_);
lean_closure_set(v___f_1150_, 5, v_xs_1142_);
v___x_1151_ = lean_array_fget(v_xs_1142_, v_k_1143_);
lean_dec(v_k_1143_);
lean_dec_ref(v_xs_1142_);
v___x_1152_ = lean_apply_1(v_f_1141_, v___x_1151_);
v___x_1153_ = lean_apply_4(v_toBind_1149_, lean_box(0), lean_box(0), v___x_1152_, v___f_1150_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1154_, lean_object* v_acc_1155_, lean_object* v_n_1156_, lean_object* v_inst_1157_, lean_object* v_f_1158_, lean_object* v_xs_1159_, lean_object* v_____do__lift_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_k_1154_, v___x_1161_);
v___x_1163_ = lean_array_push(v_acc_1155_, v_____do__lift_1160_);
v___x_1164_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1156_, v_inst_1157_, v_f_1158_, v_xs_1159_, v___x_1162_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1165_, lean_object* v_00_u03b1_1166_, lean_object* v_00_u03b2_1167_, lean_object* v_n_1168_, lean_object* v_inst_1169_, lean_object* v_f_1170_, lean_object* v_xs_1171_, lean_object* v_k_1172_, lean_object* v_h_1173_, lean_object* v_acc_1174_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1168_, v_inst_1169_, v_f_1170_, v_xs_1171_, v_k_1172_, v_acc_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1178_, lean_object* v_inst_1179_, lean_object* v_f_1180_, lean_object* v_xs_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1184_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1178_, v_inst_1179_, v_f_1180_, v_xs_1181_, v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1185_, lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_n_1188_, lean_object* v_inst_1189_, lean_object* v_f_1190_, lean_object* v_xs_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1194_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1188_, v_inst_1189_, v_f_1190_, v_xs_1191_, v___x_1192_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_apply_1(v_f_1195_, v___y_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1199_, lean_object* v_xs_1200_, lean_object* v_f_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_array_get_size(v_xs_1200_);
v___x_1204_ = lean_box(0);
v___x_1205_ = lean_nat_dec_lt(v___x_1202_, v___x_1203_);
if (v___x_1205_ == 0)
{
lean_object* v_toApplicative_1206_; lean_object* v_toPure_1207_; lean_object* v___x_1208_; 
lean_dec(v_f_1201_);
lean_dec_ref(v_xs_1200_);
v_toApplicative_1206_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc_ref(v_toApplicative_1206_);
lean_dec_ref(v_inst_1199_);
v_toPure_1207_ = lean_ctor_get(v_toApplicative_1206_, 1);
lean_inc(v_toPure_1207_);
lean_dec_ref(v_toApplicative_1206_);
v___x_1208_ = lean_apply_2(v_toPure_1207_, lean_box(0), v___x_1204_);
return v___x_1208_;
}
else
{
lean_object* v___f_1209_; uint8_t v___x_1210_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1209_, 0, v_f_1201_);
v___x_1210_ = lean_nat_dec_le(v___x_1203_, v___x_1203_);
if (v___x_1210_ == 0)
{
if (v___x_1205_ == 0)
{
lean_object* v_toApplicative_1211_; lean_object* v_toPure_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v___f_1209_);
lean_dec_ref(v_xs_1200_);
v_toApplicative_1211_ = lean_ctor_get(v_inst_1199_, 0);
lean_inc_ref(v_toApplicative_1211_);
lean_dec_ref(v_inst_1199_);
v_toPure_1212_ = lean_ctor_get(v_toApplicative_1211_, 1);
lean_inc(v_toPure_1212_);
lean_dec_ref(v_toApplicative_1211_);
v___x_1213_ = lean_apply_2(v_toPure_1212_, lean_box(0), v___x_1204_);
return v___x_1213_;
}
else
{
size_t v___x_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = lean_usize_of_nat(v___x_1203_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1199_, v___f_1209_, v_xs_1200_, v___x_1214_, v___x_1215_, v___x_1204_);
return v___x_1216_;
}
}
else
{
size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = ((size_t)0ULL);
v___x_1218_ = lean_usize_of_nat(v___x_1203_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1199_, v___f_1209_, v_xs_1200_, v___x_1217_, v___x_1218_, v___x_1204_);
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1220_, lean_object* v_00_u03b1_1221_, lean_object* v_n_1222_, lean_object* v_inst_1223_, lean_object* v_xs_1224_, lean_object* v_f_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_array_get_size(v_xs_1224_);
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_nat_dec_lt(v___x_1226_, v___x_1227_);
if (v___x_1229_ == 0)
{
lean_object* v_toApplicative_1230_; lean_object* v_toPure_1231_; lean_object* v___x_1232_; 
lean_dec(v_f_1225_);
lean_dec_ref(v_xs_1224_);
v_toApplicative_1230_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_toApplicative_1230_);
lean_dec_ref(v_inst_1223_);
v_toPure_1231_ = lean_ctor_get(v_toApplicative_1230_, 1);
lean_inc(v_toPure_1231_);
lean_dec_ref(v_toApplicative_1230_);
v___x_1232_ = lean_apply_2(v_toPure_1231_, lean_box(0), v___x_1228_);
return v___x_1232_;
}
else
{
lean_object* v___f_1233_; uint8_t v___x_1234_; 
v___f_1233_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1233_, 0, v_f_1225_);
v___x_1234_ = lean_nat_dec_le(v___x_1227_, v___x_1227_);
if (v___x_1234_ == 0)
{
if (v___x_1229_ == 0)
{
lean_object* v_toApplicative_1235_; lean_object* v_toPure_1236_; lean_object* v___x_1237_; 
lean_dec_ref(v___f_1233_);
lean_dec_ref(v_xs_1224_);
v_toApplicative_1235_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_toApplicative_1235_);
lean_dec_ref(v_inst_1223_);
v_toPure_1236_ = lean_ctor_get(v_toApplicative_1235_, 1);
lean_inc(v_toPure_1236_);
lean_dec_ref(v_toApplicative_1235_);
v___x_1237_ = lean_apply_2(v_toPure_1236_, lean_box(0), v___x_1228_);
return v___x_1237_;
}
else
{
size_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = ((size_t)0ULL);
v___x_1239_ = lean_usize_of_nat(v___x_1227_);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1223_, v___f_1233_, v_xs_1224_, v___x_1238_, v___x_1239_, v___x_1228_);
return v___x_1240_;
}
}
else
{
size_t v___x_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((size_t)0ULL);
v___x_1242_ = lean_usize_of_nat(v___x_1227_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1223_, v___f_1233_, v_xs_1224_, v___x_1241_, v___x_1242_, v___x_1228_);
return v___x_1243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1244_, lean_object* v_00_u03b1_1245_, lean_object* v_n_1246_, lean_object* v_inst_1247_, lean_object* v_xs_1248_, lean_object* v_f_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Vector_forM(v_m_1244_, v_00_u03b1_1245_, v_n_1246_, v_inst_1247_, v_xs_1248_, v_f_1249_);
lean_dec(v_n_1246_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1251_, lean_object* v_acc_1252_, lean_object* v_n_1253_, lean_object* v_inst_1254_, lean_object* v_xs_1255_, lean_object* v_f_1256_, lean_object* v_____do__lift_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1251_, v_acc_1252_, v_n_1253_, v_inst_1254_, v_xs_1255_, v_f_1256_, v_____do__lift_1257_);
lean_dec_ref(v_____do__lift_1257_);
lean_dec(v_i_1251_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1259_, lean_object* v_inst_1260_, lean_object* v_xs_1261_, lean_object* v_f_1262_, lean_object* v_i_1263_, lean_object* v_acc_1264_){
_start:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_lt(v_i_1263_, v_n_1259_);
if (v___x_1265_ == 0)
{
lean_object* v_toApplicative_1266_; lean_object* v_toPure_1267_; lean_object* v___x_1268_; 
lean_dec(v_i_1263_);
lean_dec(v_f_1262_);
lean_dec_ref(v_xs_1261_);
lean_dec(v_n_1259_);
v_toApplicative_1266_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_toApplicative_1266_);
lean_dec_ref(v_inst_1260_);
v_toPure_1267_ = lean_ctor_get(v_toApplicative_1266_, 1);
lean_inc(v_toPure_1267_);
lean_dec_ref(v_toApplicative_1266_);
v___x_1268_ = lean_apply_2(v_toPure_1267_, lean_box(0), v_acc_1264_);
return v___x_1268_;
}
else
{
lean_object* v_toBind_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_toBind_1269_ = lean_ctor_get(v_inst_1260_, 1);
lean_inc(v_toBind_1269_);
lean_inc(v_f_1262_);
lean_inc_ref(v_xs_1261_);
lean_inc(v_i_1263_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1270_, 0, v_i_1263_);
lean_closure_set(v___f_1270_, 1, v_acc_1264_);
lean_closure_set(v___f_1270_, 2, v_n_1259_);
lean_closure_set(v___f_1270_, 3, v_inst_1260_);
lean_closure_set(v___f_1270_, 4, v_xs_1261_);
lean_closure_set(v___f_1270_, 5, v_f_1262_);
v___x_1271_ = lean_array_fget(v_xs_1261_, v_i_1263_);
lean_dec(v_i_1263_);
lean_dec_ref(v_xs_1261_);
v___x_1272_ = lean_apply_1(v_f_1262_, v___x_1271_);
v___x_1273_ = lean_apply_4(v_toBind_1269_, lean_box(0), lean_box(0), v___x_1272_, v___f_1270_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1274_, lean_object* v_acc_1275_, lean_object* v_n_1276_, lean_object* v_inst_1277_, lean_object* v_xs_1278_, lean_object* v_f_1279_, lean_object* v_____do__lift_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v_i_1274_, v___x_1281_);
v___x_1283_ = l_Array_append___redArg(v_acc_1275_, v_____do__lift_1280_);
v___x_1284_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1276_, v_inst_1277_, v_xs_1278_, v_f_1279_, v___x_1282_, v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1285_, lean_object* v_00_u03b1_1286_, lean_object* v_n_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_k_1289_, lean_object* v_inst_1290_, lean_object* v_xs_1291_, lean_object* v_f_1292_, lean_object* v_i_1293_, lean_object* v_h_1294_, lean_object* v_acc_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1287_, v_inst_1290_, v_xs_1291_, v_f_1292_, v_i_1293_, v_acc_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1297_, lean_object* v_00_u03b1_1298_, lean_object* v_n_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_k_1301_, lean_object* v_inst_1302_, lean_object* v_xs_1303_, lean_object* v_f_1304_, lean_object* v_i_1305_, lean_object* v_h_1306_, lean_object* v_acc_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1297_, v_00_u03b1_1298_, v_n_1299_, v_00_u03b2_1300_, v_k_1301_, v_inst_1302_, v_xs_1303_, v_f_1304_, v_i_1305_, v_h_1306_, v_acc_1307_);
lean_dec(v_k_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1309_, lean_object* v_inst_1310_, lean_object* v_xs_1311_, lean_object* v_f_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1315_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1309_, v_inst_1310_, v_xs_1311_, v_f_1312_, v___x_1313_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1316_, lean_object* v_00_u03b1_1317_, lean_object* v_n_1318_, lean_object* v_00_u03b2_1319_, lean_object* v_k_1320_, lean_object* v_inst_1321_, lean_object* v_xs_1322_, lean_object* v_f_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1326_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1318_, v_inst_1321_, v_xs_1322_, v_f_1323_, v___x_1324_, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1327_, lean_object* v_00_u03b1_1328_, lean_object* v_n_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_k_1331_, lean_object* v_inst_1332_, lean_object* v_xs_1333_, lean_object* v_f_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Vector_flatMapM(v_m_1327_, v_00_u03b1_1328_, v_n_1329_, v_00_u03b2_1330_, v_k_1331_, v_inst_1332_, v_xs_1333_, v_f_1334_);
lean_dec(v_k_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1336_, lean_object* v_ys_1337_, lean_object* v_inst_1338_, lean_object* v_xs_1339_, lean_object* v_f_1340_, lean_object* v_n_1341_, lean_object* v_____do__lift_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1336_, v_ys_1337_, v_inst_1338_, v_xs_1339_, v_f_1340_, v_n_1341_, v_____do__lift_1342_);
lean_dec(v_n_1341_);
lean_dec(v_j_1336_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1344_, lean_object* v_xs_1345_, lean_object* v_f_1346_, lean_object* v_i_1347_, lean_object* v_j_1348_, lean_object* v_ys_1349_){
_start:
{
lean_object* v_toApplicative_1350_; lean_object* v_toBind_1351_; lean_object* v_toPure_1352_; lean_object* v_zero_1353_; uint8_t v_isZero_1354_; 
v_toApplicative_1350_ = lean_ctor_get(v_inst_1344_, 0);
v_toBind_1351_ = lean_ctor_get(v_inst_1344_, 1);
lean_inc(v_toBind_1351_);
v_toPure_1352_ = lean_ctor_get(v_toApplicative_1350_, 1);
v_zero_1353_ = lean_unsigned_to_nat(0u);
v_isZero_1354_ = lean_nat_dec_eq(v_i_1347_, v_zero_1353_);
if (v_isZero_1354_ == 1)
{
lean_object* v___x_1355_; 
lean_inc(v_toPure_1352_);
lean_dec(v_toBind_1351_);
lean_dec(v_j_1348_);
lean_dec(v_f_1346_);
lean_dec_ref(v_xs_1345_);
lean_dec_ref(v_inst_1344_);
v___x_1355_ = lean_apply_2(v_toPure_1352_, lean_box(0), v_ys_1349_);
return v___x_1355_;
}
else
{
lean_object* v_one_1356_; lean_object* v_n_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_one_1356_ = lean_unsigned_to_nat(1u);
v_n_1357_ = lean_nat_sub(v_i_1347_, v_one_1356_);
lean_inc(v_f_1346_);
lean_inc_ref(v_xs_1345_);
lean_inc(v_j_1348_);
v___f_1358_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1358_, 0, v_j_1348_);
lean_closure_set(v___f_1358_, 1, v_ys_1349_);
lean_closure_set(v___f_1358_, 2, v_inst_1344_);
lean_closure_set(v___f_1358_, 3, v_xs_1345_);
lean_closure_set(v___f_1358_, 4, v_f_1346_);
lean_closure_set(v___f_1358_, 5, v_n_1357_);
v___x_1359_ = lean_array_fget(v_xs_1345_, v_j_1348_);
lean_dec_ref(v_xs_1345_);
v___x_1360_ = lean_apply_3(v_f_1346_, v_j_1348_, v___x_1359_, lean_box(0));
v___x_1361_ = lean_apply_4(v_toBind_1351_, lean_box(0), lean_box(0), v___x_1360_, v___f_1358_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1362_, lean_object* v_ys_1363_, lean_object* v_inst_1364_, lean_object* v_xs_1365_, lean_object* v_f_1366_, lean_object* v_n_1367_, lean_object* v_____do__lift_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_add(v_j_1362_, v___x_1369_);
v___x_1371_ = lean_array_push(v_ys_1363_, v_____do__lift_1368_);
v___x_1372_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1364_, v_xs_1365_, v_f_1366_, v_n_1367_, v___x_1370_, v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1373_, lean_object* v_xs_1374_, lean_object* v_f_1375_, lean_object* v_i_1376_, lean_object* v_j_1377_, lean_object* v_ys_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1373_, v_xs_1374_, v_f_1375_, v_i_1376_, v_j_1377_, v_ys_1378_);
lean_dec(v_i_1376_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1380_, lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_m_1383_, lean_object* v_inst_1384_, lean_object* v_xs_1385_, lean_object* v_f_1386_, lean_object* v_i_1387_, lean_object* v_j_1388_, lean_object* v_inv_1389_, lean_object* v_ys_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1384_, v_xs_1385_, v_f_1386_, v_i_1387_, v_j_1388_, v_ys_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1392_, lean_object* v_00_u03b1_1393_, lean_object* v_00_u03b2_1394_, lean_object* v_m_1395_, lean_object* v_inst_1396_, lean_object* v_xs_1397_, lean_object* v_f_1398_, lean_object* v_i_1399_, lean_object* v_j_1400_, lean_object* v_inv_1401_, lean_object* v_ys_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Vector_mapFinIdxM_map(v_n_1392_, v_00_u03b1_1393_, v_00_u03b2_1394_, v_m_1395_, v_inst_1396_, v_xs_1397_, v_f_1398_, v_i_1399_, v_j_1400_, v_inv_1401_, v_ys_1402_);
lean_dec(v_i_1399_);
lean_dec(v_n_1392_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1404_, lean_object* v_inst_1405_, lean_object* v_xs_1406_, lean_object* v_f_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1410_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1405_, v_xs_1406_, v_f_1407_, v_n_1404_, v___x_1408_, v___x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1411_, lean_object* v_inst_1412_, lean_object* v_xs_1413_, lean_object* v_f_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Vector_mapFinIdxM___redArg(v_n_1411_, v_inst_1412_, v_xs_1413_, v_f_1414_);
lean_dec(v_n_1411_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1416_, lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_m_1419_, lean_object* v_inst_1420_, lean_object* v_xs_1421_, lean_object* v_f_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1425_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1420_, v_xs_1421_, v_f_1422_, v_n_1416_, v___x_1423_, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1426_, lean_object* v_00_u03b1_1427_, lean_object* v_00_u03b2_1428_, lean_object* v_m_1429_, lean_object* v_inst_1430_, lean_object* v_xs_1431_, lean_object* v_f_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Vector_mapFinIdxM(v_n_1426_, v_00_u03b1_1427_, v_00_u03b2_1428_, v_m_1429_, v_inst_1430_, v_xs_1431_, v_f_1432_);
lean_dec(v_n_1426_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1434_, lean_object* v_inst_1435_, lean_object* v_f_1436_, lean_object* v_xs_1437_){
_start:
{
lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___f_1438_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1438_, 0, v_f_1436_);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1441_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1435_, v_xs_1437_, v___f_1438_, v_n_1434_, v___x_1439_, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1442_, lean_object* v_inst_1443_, lean_object* v_f_1444_, lean_object* v_xs_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Vector_mapIdxM___redArg(v_n_1442_, v_inst_1443_, v_f_1444_, v_xs_1445_);
lean_dec(v_n_1442_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1447_, lean_object* v_00_u03b1_1448_, lean_object* v_00_u03b2_1449_, lean_object* v_m_1450_, lean_object* v_inst_1451_, lean_object* v_f_1452_, lean_object* v_xs_1453_){
_start:
{
lean_object* v___f_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___f_1454_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1454_, 0, v_f_1452_);
v___x_1455_ = lean_unsigned_to_nat(0u);
v___x_1456_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1457_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1451_, v_xs_1453_, v___f_1454_, v_n_1447_, v___x_1455_, v___x_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1458_, lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_m_1461_, lean_object* v_inst_1462_, lean_object* v_f_1463_, lean_object* v_xs_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Vector_mapIdxM(v_n_1458_, v_00_u03b1_1459_, v_00_u03b2_1460_, v_m_1461_, v_inst_1462_, v_f_1463_, v_xs_1464_);
lean_dec(v_n_1458_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1466_, lean_object* v_f_1467_, lean_object* v_xs_1468_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1466_, v_f_1467_, v_xs_1468_, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1471_, lean_object* v_n_1472_, lean_object* v_00_u03b1_1473_, lean_object* v_m_1474_, lean_object* v_inst_1475_, lean_object* v_f_1476_, lean_object* v_xs_1477_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_unsigned_to_nat(0u);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1475_, v_f_1476_, v_xs_1477_, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_n_1481_, lean_object* v_00_u03b1_1482_, lean_object* v_m_1483_, lean_object* v_inst_1484_, lean_object* v_f_1485_, lean_object* v_xs_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Vector_firstM(v_00_u03b2_1480_, v_n_1481_, v_00_u03b1_1482_, v_m_1483_, v_inst_1484_, v_f_1485_, v_xs_1486_);
lean_dec(v_n_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1488_){
_start:
{
lean_inc_ref(v_x_1488_);
return v_x_1488_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Vector_flatten___redArg___lam__0(v_x_1489_);
lean_dec_ref(v_x_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1495_){
_start:
{
lean_object* v___f_1496_; lean_object* v___x_1497_; size_t v_sz_1498_; size_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___f_1496_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1497_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1498_ = lean_array_size(v_xs_1495_);
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1497_, v___f_1496_, v_sz_1498_, v___x_1499_, v_xs_1495_);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1503_ = lean_array_get_size(v___x_1500_);
v___x_1504_ = lean_nat_dec_lt(v___x_1501_, v___x_1503_);
if (v___x_1504_ == 0)
{
lean_dec(v___x_1500_);
return v___x_1502_;
}
else
{
lean_object* v___f_1505_; uint8_t v___x_1506_; 
v___f_1505_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1506_ = lean_nat_dec_le(v___x_1503_, v___x_1503_);
if (v___x_1506_ == 0)
{
if (v___x_1504_ == 0)
{
lean_dec(v___x_1500_);
return v___x_1502_;
}
else
{
size_t v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_usize_of_nat(v___x_1503_);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1497_, v___f_1505_, v___x_1500_, v___x_1499_, v___x_1507_, v___x_1502_);
return v___x_1508_;
}
}
else
{
size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = lean_usize_of_nat(v___x_1503_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1497_, v___f_1505_, v___x_1500_, v___x_1499_, v___x_1509_, v___x_1502_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1511_, lean_object* v_n_1512_, lean_object* v_m_1513_, lean_object* v_xs_1514_){
_start:
{
lean_object* v___f_1515_; lean_object* v___x_1516_; size_t v_sz_1517_; size_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___f_1515_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1516_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1517_ = lean_array_size(v_xs_1514_);
v___x_1518_ = ((size_t)0ULL);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v___f_1515_, v_sz_1517_, v___x_1518_, v_xs_1514_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v___x_1521_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1522_ = lean_array_get_size(v___x_1519_);
v___x_1523_ = lean_nat_dec_lt(v___x_1520_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec(v___x_1519_);
return v___x_1521_;
}
else
{
lean_object* v___f_1524_; uint8_t v___x_1525_; 
v___f_1524_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1525_ = lean_nat_dec_le(v___x_1522_, v___x_1522_);
if (v___x_1525_ == 0)
{
if (v___x_1523_ == 0)
{
lean_dec(v___x_1519_);
return v___x_1521_;
}
else
{
size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_usize_of_nat(v___x_1522_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v___f_1524_, v___x_1519_, v___x_1518_, v___x_1526_, v___x_1521_);
return v___x_1527_;
}
}
else
{
size_t v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = lean_usize_of_nat(v___x_1522_);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v___f_1524_, v___x_1519_, v___x_1518_, v___x_1528_, v___x_1521_);
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_n_1531_, lean_object* v_m_1532_, lean_object* v_xs_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Vector_flatten(v_00_u03b1_1530_, v_n_1531_, v_m_1532_, v_xs_1533_);
lean_dec(v_m_1532_);
lean_dec(v_n_1531_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1535_, lean_object* v_x1_1536_, lean_object* v_x2_1537_){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_apply_1(v_f_1535_, v_x2_1537_);
v___x_1539_ = l_Array_append___redArg(v_x1_1536_, v___x_1538_);
lean_dec_ref(v___x_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1540_, lean_object* v_f_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1542_ = lean_unsigned_to_nat(0u);
v___x_1543_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1544_ = lean_array_get_size(v_xs_1540_);
v___x_1545_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1546_ = lean_nat_dec_lt(v___x_1542_, v___x_1544_);
if (v___x_1546_ == 0)
{
lean_dec_ref(v_f_1541_);
lean_dec_ref(v_xs_1540_);
return v___x_1543_;
}
else
{
lean_object* v___f_1547_; uint8_t v___x_1548_; 
v___f_1547_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1547_, 0, v_f_1541_);
v___x_1548_ = lean_nat_dec_le(v___x_1544_, v___x_1544_);
if (v___x_1548_ == 0)
{
if (v___x_1546_ == 0)
{
lean_dec_ref(v___f_1547_);
lean_dec_ref(v_xs_1540_);
return v___x_1543_;
}
else
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = lean_usize_of_nat(v___x_1544_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1545_, v___f_1547_, v_xs_1540_, v___x_1549_, v___x_1550_, v___x_1543_);
return v___x_1551_;
}
}
else
{
size_t v___x_1552_; size_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = lean_usize_of_nat(v___x_1544_);
v___x_1554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1545_, v___f_1547_, v_xs_1540_, v___x_1552_, v___x_1553_, v___x_1543_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1555_, lean_object* v_n_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_m_1558_, lean_object* v_xs_1559_, lean_object* v_f_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1563_ = lean_array_get_size(v_xs_1559_);
v___x_1564_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1565_ = lean_nat_dec_lt(v___x_1561_, v___x_1563_);
if (v___x_1565_ == 0)
{
lean_dec_ref(v_f_1560_);
lean_dec_ref(v_xs_1559_);
return v___x_1562_;
}
else
{
lean_object* v___f_1566_; uint8_t v___x_1567_; 
v___f_1566_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1566_, 0, v_f_1560_);
v___x_1567_ = lean_nat_dec_le(v___x_1563_, v___x_1563_);
if (v___x_1567_ == 0)
{
if (v___x_1565_ == 0)
{
lean_dec_ref(v___f_1566_);
lean_dec_ref(v_xs_1559_);
return v___x_1562_;
}
else
{
size_t v___x_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = lean_usize_of_nat(v___x_1563_);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1564_, v___f_1566_, v_xs_1559_, v___x_1568_, v___x_1569_, v___x_1562_);
return v___x_1570_;
}
}
else
{
size_t v___x_1571_; size_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = ((size_t)0ULL);
v___x_1572_ = lean_usize_of_nat(v___x_1563_);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1564_, v___f_1566_, v_xs_1559_, v___x_1571_, v___x_1572_, v___x_1562_);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1574_, lean_object* v_n_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_m_1577_, lean_object* v_xs_1578_, lean_object* v_f_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Vector_flatMap(v_00_u03b1_1574_, v_n_1575_, v_00_u03b2_1576_, v_m_1577_, v_xs_1578_, v_f_1579_);
lean_dec(v_m_1577_);
lean_dec(v_n_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1581_, lean_object* v_k_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Array_zipIdx___redArg(v_xs_1581_, v_k_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1584_, lean_object* v_k_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Vector_zipIdx___redArg(v_xs_1584_, v_k_1585_);
lean_dec(v_k_1585_);
lean_dec_ref(v_xs_1584_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1587_, lean_object* v_n_1588_, lean_object* v_xs_1589_, lean_object* v_k_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Array_zipIdx___redArg(v_xs_1589_, v_k_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_n_1593_, lean_object* v_xs_1594_, lean_object* v_k_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Vector_zipIdx(v_00_u03b1_1592_, v_n_1593_, v_xs_1594_, v_k_1595_);
lean_dec(v_k_1595_);
lean_dec_ref(v_xs_1594_);
lean_dec(v_n_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1597_, lean_object* v_bs_1598_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Array_zip___redArg(v_as_1597_, v_bs_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1600_, lean_object* v_bs_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Vector_zip___redArg(v_as_1600_, v_bs_1601_);
lean_dec_ref(v_bs_1601_);
lean_dec_ref(v_as_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1603_, lean_object* v_n_1604_, lean_object* v_00_u03b2_1605_, lean_object* v_as_1606_, lean_object* v_bs_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Array_zip___redArg(v_as_1606_, v_bs_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1609_, lean_object* v_n_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_as_1612_, lean_object* v_bs_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Vector_zip(v_00_u03b1_1609_, v_n_1610_, v_00_u03b2_1611_, v_as_1612_, v_bs_1613_);
lean_dec_ref(v_bs_1613_);
lean_dec_ref(v_as_1612_);
lean_dec(v_n_1610_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1615_, lean_object* v_as_1616_, lean_object* v_bs_1617_){
_start:
{
lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___f_1618_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1618_, 0, v_f_1615_);
v___x_1619_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1622_ = l_Array_zipWithMAux___redArg(v___x_1619_, v_as_1616_, v_bs_1617_, v___f_1618_, v___x_1620_, v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1623_, lean_object* v_00_u03b2_1624_, lean_object* v_00_u03c6_1625_, lean_object* v_n_1626_, lean_object* v_f_1627_, lean_object* v_as_1628_, lean_object* v_bs_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___f_1630_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1630_, 0, v_f_1627_);
v___x_1631_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1634_ = l_Array_zipWithMAux___redArg(v___x_1631_, v_as_1628_, v_bs_1629_, v___f_1630_, v___x_1632_, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_00_u03c6_1637_, lean_object* v_n_1638_, lean_object* v_f_1639_, lean_object* v_as_1640_, lean_object* v_bs_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Vector_zipWith(v_00_u03b1_1635_, v_00_u03b2_1636_, v_00_u03c6_1637_, v_n_1638_, v_f_1639_, v_as_1640_, v_bs_1641_);
lean_dec(v_n_1638_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v_fst_1645_; lean_object* v_snd_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v___x_1644_ = l_Array_unzip___redArg(v_xs_1643_);
v_fst_1645_ = lean_ctor_get(v___x_1644_, 0);
v_snd_1646_ = lean_ctor_get(v___x_1644_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1644_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snd_1646_);
lean_inc(v_fst_1645_);
lean_dec(v___x_1644_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_fst_1645_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_snd_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Vector_unzip___redArg(v_xs_1654_);
lean_dec_ref(v_xs_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_n_1658_, lean_object* v_xs_1659_){
_start:
{
lean_object* v___x_1660_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
v___x_1660_ = l_Array_unzip___redArg(v_xs_1659_);
v_fst_1661_ = lean_ctor_get(v___x_1660_, 0);
v_snd_1662_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snd_1662_);
lean_inc(v_fst_1661_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_fst_1661_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_snd_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_00_u03b2_1671_, lean_object* v_n_1672_, lean_object* v_xs_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Vector_unzip(v_00_u03b1_1670_, v_00_u03b2_1671_, v_n_1672_, v_xs_1673_);
lean_dec_ref(v_xs_1673_);
lean_dec(v_n_1672_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1675_, lean_object* v_f_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Array_ofFn___redArg(v_n_1675_, v_f_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1678_, lean_object* v_00_u03b1_1679_, lean_object* v_f_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Array_ofFn___redArg(v_n_1678_, v_f_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1682_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1684_, lean_object* v_i_1685_, lean_object* v_j_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_array_fswap(v_xs_1684_, v_i_1685_, v_j_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1688_, lean_object* v_i_1689_, lean_object* v_j_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Vector_swap___redArg(v_xs_1688_, v_i_1689_, v_j_1690_);
lean_dec(v_j_1690_);
lean_dec(v_i_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1692_, lean_object* v_n_1693_, lean_object* v_xs_1694_, lean_object* v_i_1695_, lean_object* v_j_1696_, lean_object* v_hi_1697_, lean_object* v_hj_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_array_fswap(v_xs_1694_, v_i_1695_, v_j_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_n_1701_, lean_object* v_xs_1702_, lean_object* v_i_1703_, lean_object* v_j_1704_, lean_object* v_hi_1705_, lean_object* v_hj_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Vector_swap(v_00_u03b1_1700_, v_n_1701_, v_xs_1702_, v_i_1703_, v_j_1704_, v_hi_1705_, v_hj_1706_);
lean_dec(v_j_1704_);
lean_dec(v_i_1703_);
lean_dec(v_n_1701_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1708_, lean_object* v_i_1709_, lean_object* v_j_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_array_swap(v_xs_1708_, v_i_1709_, v_j_1710_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1712_, lean_object* v_i_1713_, lean_object* v_j_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Vector_swapIfInBounds___redArg(v_xs_1712_, v_i_1713_, v_j_1714_);
lean_dec(v_j_1714_);
lean_dec(v_i_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1716_, lean_object* v_n_1717_, lean_object* v_xs_1718_, lean_object* v_i_1719_, lean_object* v_j_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = lean_array_swap(v_xs_1718_, v_i_1719_, v_j_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_n_1723_, lean_object* v_xs_1724_, lean_object* v_i_1725_, lean_object* v_j_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Vector_swapIfInBounds(v_00_u03b1_1722_, v_n_1723_, v_xs_1724_, v_i_1725_, v_j_1726_);
lean_dec(v_j_1726_);
lean_dec(v_i_1725_);
lean_dec(v_n_1723_);
return v_res_1727_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1729_, lean_object* v_i_1730_, lean_object* v_x_1731_){
_start:
{
lean_object* v_e_1732_; lean_object* v_xs_x27_1733_; lean_object* v___x_1734_; 
v_e_1732_ = lean_array_fget(v_xs_1729_, v_i_1730_);
v_xs_x27_1733_ = lean_array_fset(v_xs_1729_, v_i_1730_, v_x_1731_);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_e_1732_);
lean_ctor_set(v___x_1734_, 1, v_xs_x27_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1735_, lean_object* v_i_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Vector_swapAt___redArg(v_xs_1735_, v_i_1736_, v_x_1737_);
lean_dec(v_i_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1739_, lean_object* v_n_1740_, lean_object* v_xs_1741_, lean_object* v_i_1742_, lean_object* v_x_1743_, lean_object* v_hi_1744_){
_start:
{
lean_object* v_e_1745_; lean_object* v_xs_x27_1746_; lean_object* v___x_1747_; 
v_e_1745_ = lean_array_fget(v_xs_1741_, v_i_1742_);
v_xs_x27_1746_ = lean_array_fset(v_xs_1741_, v_i_1742_, v_x_1743_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v_e_1745_);
lean_ctor_set(v___x_1747_, 1, v_xs_x27_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1748_, lean_object* v_n_1749_, lean_object* v_xs_1750_, lean_object* v_i_1751_, lean_object* v_x_1752_, lean_object* v_hi_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Vector_swapAt(v_00_u03b1_1748_, v_n_1749_, v_xs_1750_, v_i_1751_, v_x_1752_, v_hi_1753_);
lean_dec(v_i_1751_);
lean_dec(v_n_1749_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1759_, lean_object* v_i_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_array_get_size(v_xs_1759_);
v___x_1763_ = lean_nat_dec_lt(v_i_1760_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v_this_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_fst_1776_; lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
v_this_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1764_, 0, v_x_1761_);
lean_ctor_set(v_this_1764_, 1, v_xs_1759_);
v___x_1765_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1766_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1767_ = lean_unsigned_to_nat(438u);
v___x_1768_ = lean_unsigned_to_nat(4u);
v___x_1769_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1770_ = l_Nat_reprFast(v_i_1760_);
v___x_1771_ = lean_string_append(v___x_1769_, v___x_1770_);
lean_dec_ref(v___x_1770_);
v___x_1772_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
v___x_1774_ = l_mkPanicMessageWithDecl(v___x_1765_, v___x_1766_, v___x_1767_, v___x_1768_, v___x_1773_);
lean_dec_ref(v___x_1773_);
v___x_1775_ = l_panic___redArg(v_this_1764_, v___x_1774_);
lean_dec_ref(v_this_1764_);
v_fst_1776_ = lean_ctor_get(v___x_1775_, 0);
v_snd_1777_ = lean_ctor_get(v___x_1775_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1775_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_inc(v_fst_1776_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_fst_1776_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_snd_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
else
{
lean_object* v_e_1785_; lean_object* v_xs_x27_1786_; lean_object* v___x_1787_; 
v_e_1785_ = lean_array_fget(v_xs_1759_, v_i_1760_);
v_xs_x27_1786_ = lean_array_fset(v_xs_1759_, v_i_1760_, v_x_1761_);
lean_dec(v_i_1760_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_e_1785_);
lean_ctor_set(v___x_1787_, 1, v_xs_x27_1786_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1788_, lean_object* v_n_1789_, lean_object* v_xs_1790_, lean_object* v_i_1791_, lean_object* v_x_1792_){
_start:
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = lean_array_get_size(v_xs_1790_);
v___x_1794_ = lean_nat_dec_lt(v_i_1791_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v_this_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_fst_1807_; lean_object* v_snd_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_this_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1795_, 0, v_x_1792_);
lean_ctor_set(v_this_1795_, 1, v_xs_1790_);
v___x_1796_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1797_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1798_ = lean_unsigned_to_nat(438u);
v___x_1799_ = lean_unsigned_to_nat(4u);
v___x_1800_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1801_ = l_Nat_reprFast(v_i_1791_);
v___x_1802_ = lean_string_append(v___x_1800_, v___x_1801_);
lean_dec_ref(v___x_1801_);
v___x_1803_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1804_ = lean_string_append(v___x_1802_, v___x_1803_);
v___x_1805_ = l_mkPanicMessageWithDecl(v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v___x_1804_);
lean_dec_ref(v___x_1804_);
v___x_1806_ = l_panic___redArg(v_this_1795_, v___x_1805_);
lean_dec_ref(v_this_1795_);
v_fst_1807_ = lean_ctor_get(v___x_1806_, 0);
v_snd_1808_ = lean_ctor_get(v___x_1806_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1806_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snd_1808_);
lean_inc(v_fst_1807_);
lean_dec(v___x_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_fst_1807_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_snd_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
lean_object* v_e_1816_; lean_object* v_xs_x27_1817_; lean_object* v___x_1818_; 
v_e_1816_ = lean_array_fget(v_xs_1790_, v_i_1791_);
v_xs_x27_1817_ = lean_array_fset(v_xs_1790_, v_i_1791_, v_x_1792_);
lean_dec(v_i_1791_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_e_1816_);
lean_ctor_set(v___x_1818_, 1, v_xs_x27_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_n_1820_, lean_object* v_xs_1821_, lean_object* v_i_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Vector_swapAt_x21(v_00_u03b1_1819_, v_n_1820_, v_xs_1821_, v_i_1822_, v_x_1823_);
lean_dec(v_n_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Array_range(v_n_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1827_, lean_object* v_size_1828_, lean_object* v_step_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Array_range_x27(v_start_1827_, v_size_1828_, v_step_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1831_, lean_object* v_xs_1832_, lean_object* v_ys_1833_, lean_object* v_r_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Array_isEqvAux___redArg(v_xs_1832_, v_ys_1833_, v_r_1834_, v_n_1831_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1836_, lean_object* v_xs_1837_, lean_object* v_ys_1838_, lean_object* v_r_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Vector_isEqv___redArg(v_n_1836_, v_xs_1837_, v_ys_1838_, v_r_1839_);
lean_dec_ref(v_ys_1838_);
lean_dec_ref(v_xs_1837_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1842_, lean_object* v_n_1843_, lean_object* v_xs_1844_, lean_object* v_ys_1845_, lean_object* v_r_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Array_isEqvAux___redArg(v_xs_1844_, v_ys_1845_, v_r_1846_, v_n_1843_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1848_, lean_object* v_n_1849_, lean_object* v_xs_1850_, lean_object* v_ys_1851_, lean_object* v_r_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_Vector_isEqv(v_00_u03b1_1848_, v_n_1849_, v_xs_1850_, v_ys_1851_, v_r_1852_);
lean_dec_ref(v_ys_1851_);
lean_dec_ref(v_xs_1850_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1855_, lean_object* v_x1_1856_, lean_object* v_x2_1857_){
_start:
{
lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1858_ = lean_apply_2(v_inst_1855_, v_x1_1856_, v_x2_1857_);
v___x_1859_ = lean_unbox(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1860_, lean_object* v_x1_1861_, lean_object* v_x2_1862_){
_start:
{
uint8_t v_res_1863_; lean_object* v_r_1864_; 
v_res_1863_ = l_Vector_instBEq___redArg___lam__0(v_inst_1860_, v_x1_1861_, v_x2_1862_);
v_r_1864_ = lean_box(v_res_1863_);
return v_r_1864_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1865_, lean_object* v_n_1866_, lean_object* v_xs_1867_, lean_object* v_ys_1868_){
_start:
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Array_isEqvAux___redArg(v_xs_1867_, v_ys_1868_, v___f_1865_, v_n_1866_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1870_, lean_object* v_n_1871_, lean_object* v_xs_1872_, lean_object* v_ys_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Vector_instBEq___redArg___lam__1(v___f_1870_, v_n_1871_, v_xs_1872_, v_ys_1873_);
lean_dec_ref(v_ys_1873_);
lean_dec_ref(v_xs_1872_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1876_, lean_object* v_inst_1877_){
_start:
{
lean_object* v___f_1878_; lean_object* v___f_1879_; 
v___f_1878_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1878_, 0, v_inst_1877_);
v___f_1879_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1879_, 0, v___f_1878_);
lean_closure_set(v___f_1879_, 1, v_n_1876_);
return v___f_1879_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1880_, lean_object* v_n_1881_, lean_object* v_inst_1882_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Vector_instBEq___redArg(v_n_1881_, v_inst_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Array_reverse___redArg(v_xs_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1886_, lean_object* v_n_1887_, lean_object* v_xs_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Array_reverse___redArg(v_xs_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1890_, lean_object* v_n_1891_, lean_object* v_xs_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Vector_reverse(v_00_u03b1_1890_, v_n_1891_, v_xs_1892_);
lean_dec(v_n_1891_);
return v_res_1893_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1895_, lean_object* v_i_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Array_eraseIdx___redArg(v_xs_1895_, v_i_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1898_, lean_object* v_n_1899_, lean_object* v_xs_1900_, lean_object* v_i_1901_, lean_object* v_h_1902_){
_start:
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Array_eraseIdx___redArg(v_xs_1900_, v_i_1901_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1904_, lean_object* v_n_1905_, lean_object* v_xs_1906_, lean_object* v_i_1907_, lean_object* v_h_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Vector_eraseIdx(v_00_u03b1_1904_, v_n_1905_, v_xs_1906_, v_i_1907_, v_h_1908_);
lean_dec(v_n_1905_);
return v_res_1909_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1913_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1914_ = lean_unsigned_to_nat(4u);
v___x_1915_ = lean_unsigned_to_nat(395u);
v___x_1916_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1917_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1918_ = l_mkPanicMessageWithDecl(v___x_1917_, v___x_1916_, v___x_1915_, v___x_1914_, v___x_1913_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1919_, lean_object* v_xs_1920_, lean_object* v_i_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_nat_dec_lt(v_i_1921_, v_n_1919_);
if (v___x_1922_ == 0)
{
lean_object* v_this_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec(v_i_1921_);
v_this_1923_ = lean_array_pop(v_xs_1920_);
v___x_1924_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1925_ = l_panic___redArg(v_this_1923_, v___x_1924_);
lean_dec_ref(v_this_1923_);
return v___x_1925_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Array_eraseIdx___redArg(v_xs_1920_, v_i_1921_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1927_, lean_object* v_xs_1928_, lean_object* v_i_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Vector_eraseIdx_x21___redArg(v_n_1927_, v_xs_1928_, v_i_1929_);
lean_dec(v_n_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1931_, lean_object* v_n_1932_, lean_object* v_xs_1933_, lean_object* v_i_1934_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_nat_dec_lt(v_i_1934_, v_n_1932_);
if (v___x_1935_ == 0)
{
lean_object* v_this_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_dec(v_i_1934_);
v_this_1936_ = lean_array_pop(v_xs_1933_);
v___x_1937_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1938_ = l_panic___redArg(v_this_1936_, v___x_1937_);
lean_dec_ref(v_this_1936_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Array_eraseIdx___redArg(v_xs_1933_, v_i_1934_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1940_, lean_object* v_n_1941_, lean_object* v_xs_1942_, lean_object* v_i_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Vector_eraseIdx_x21(v_00_u03b1_1940_, v_n_1941_, v_xs_1942_, v_i_1943_);
lean_dec(v_n_1941_);
return v_res_1944_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1946_, lean_object* v_i_1947_, lean_object* v_x_1948_){
_start:
{
lean_object* v_j_1949_; lean_object* v_as_1950_; lean_object* v___x_1951_; 
v_j_1949_ = lean_array_get_size(v_xs_1946_);
v_as_1950_ = lean_array_push(v_xs_1946_, v_x_1948_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1947_, v_as_1950_, v_j_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1952_, lean_object* v_i_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Vector_insertIdx___redArg(v_xs_1952_, v_i_1953_, v_x_1954_);
lean_dec(v_i_1953_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1956_, lean_object* v_n_1957_, lean_object* v_xs_1958_, lean_object* v_i_1959_, lean_object* v_x_1960_, lean_object* v_h_1961_){
_start:
{
lean_object* v_j_1962_; lean_object* v_as_1963_; lean_object* v___x_1964_; 
v_j_1962_ = lean_array_get_size(v_xs_1958_);
v_as_1963_ = lean_array_push(v_xs_1958_, v_x_1960_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1959_, v_as_1963_, v_j_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1965_, lean_object* v_n_1966_, lean_object* v_xs_1967_, lean_object* v_i_1968_, lean_object* v_x_1969_, lean_object* v_h_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Vector_insertIdx(v_00_u03b1_1965_, v_n_1966_, v_xs_1967_, v_i_1968_, v_x_1969_, v_h_1970_);
lean_dec(v_i_1968_);
lean_dec(v_n_1966_);
return v_res_1971_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1973_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1974_ = lean_unsigned_to_nat(4u);
v___x_1975_ = lean_unsigned_to_nat(408u);
v___x_1976_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1977_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1978_ = l_mkPanicMessageWithDecl(v___x_1977_, v___x_1976_, v___x_1975_, v___x_1974_, v___x_1973_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1979_, lean_object* v_xs_1980_, lean_object* v_i_1981_, lean_object* v_x_1982_){
_start:
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_nat_dec_le(v_i_1981_, v_n_1979_);
if (v___x_1983_ == 0)
{
lean_object* v_this_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_this_1984_ = lean_array_push(v_xs_1980_, v_x_1982_);
v___x_1985_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1986_ = l_panic___redArg(v_this_1984_, v___x_1985_);
lean_dec_ref(v_this_1984_);
return v___x_1986_;
}
else
{
lean_object* v_j_1987_; lean_object* v_as_1988_; lean_object* v___x_1989_; 
v_j_1987_ = lean_array_get_size(v_xs_1980_);
v_as_1988_ = lean_array_push(v_xs_1980_, v_x_1982_);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1981_, v_as_1988_, v_j_1987_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1990_, lean_object* v_xs_1991_, lean_object* v_i_1992_, lean_object* v_x_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Vector_insertIdx_x21___redArg(v_n_1990_, v_xs_1991_, v_i_1992_, v_x_1993_);
lean_dec(v_i_1992_);
lean_dec(v_n_1990_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1995_, lean_object* v_n_1996_, lean_object* v_xs_1997_, lean_object* v_i_1998_, lean_object* v_x_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_nat_dec_le(v_i_1998_, v_n_1996_);
if (v___x_2000_ == 0)
{
lean_object* v_this_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v_this_2001_ = lean_array_push(v_xs_1997_, v_x_1999_);
v___x_2002_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_2003_ = l_panic___redArg(v_this_2001_, v___x_2002_);
lean_dec_ref(v_this_2001_);
return v___x_2003_;
}
else
{
lean_object* v_j_2004_; lean_object* v_as_2005_; lean_object* v___x_2006_; 
v_j_2004_ = lean_array_get_size(v_xs_1997_);
v_as_2005_ = lean_array_push(v_xs_1997_, v_x_1999_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1998_, v_as_2005_, v_j_2004_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_2007_, lean_object* v_n_2008_, lean_object* v_xs_2009_, lean_object* v_i_2010_, lean_object* v_x_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Vector_insertIdx_x21(v_00_u03b1_2007_, v_n_2008_, v_xs_2009_, v_i_2010_, v_x_2011_);
lean_dec(v_i_2010_);
lean_dec(v_n_2008_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_2013_, lean_object* v_xs_2014_){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = l_Array_extract___redArg(v_xs_2014_, v___x_2015_, v_n_2013_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_2017_, lean_object* v_xs_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Vector_tail___redArg(v_n_2017_, v_xs_2018_);
lean_dec_ref(v_xs_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_2020_, lean_object* v_n_2021_, lean_object* v_xs_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2023_ = lean_unsigned_to_nat(1u);
v___x_2024_ = l_Array_extract___redArg(v_xs_2022_, v___x_2023_, v_n_2021_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_n_2026_, lean_object* v_xs_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Vector_tail(v_00_u03b1_2025_, v_n_2026_, v_xs_2027_);
lean_dec_ref(v_xs_2027_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2029_, lean_object* v_xs_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Array_finIdxOf_x3f___redArg(v_inst_2029_, v_xs_2030_, v_x_2031_);
if (lean_obj_tag(v___x_2032_) == 0)
{
return v___x_2032_;
}
else
{
lean_object* v_val_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_val_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_val_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_val_2033_);
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
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2041_, lean_object* v_xs_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2041_, v_xs_2042_, v_x_2043_);
lean_dec_ref(v_xs_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2045_, lean_object* v_n_2046_, lean_object* v_inst_2047_, lean_object* v_xs_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Array_finIdxOf_x3f___redArg(v_inst_2047_, v_xs_2048_, v_x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
return v___x_2050_;
}
else
{
lean_object* v_val_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_val_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_val_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_val_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2059_, lean_object* v_n_2060_, lean_object* v_inst_2061_, lean_object* v_xs_2062_, lean_object* v_x_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2059_, v_n_2060_, v_inst_2061_, v_xs_2062_, v_x_2063_);
lean_dec_ref(v_xs_2062_);
lean_dec(v_n_2060_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2065_, lean_object* v_xs_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2065_, v_xs_2066_, v___x_2067_);
if (lean_obj_tag(v___x_2068_) == 0)
{
return v___x_2068_;
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_val_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_val_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_val_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2077_, lean_object* v_xs_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Vector_findFinIdx_x3f___redArg(v_p_2077_, v_xs_2078_);
lean_dec_ref(v_xs_2078_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2080_, lean_object* v_n_2081_, lean_object* v_p_2082_, lean_object* v_xs_2083_){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2082_, v_xs_2083_, v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
return v___x_2085_;
}
else
{
lean_object* v_val_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
v_val_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_val_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_val_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2094_, lean_object* v_n_2095_, lean_object* v_p_2096_, lean_object* v_xs_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2094_, v_n_2095_, v_p_2096_, v_xs_2097_);
lean_dec_ref(v_xs_2097_);
lean_dec(v_n_2095_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2099_, lean_object* v_____s_2100_){
_start:
{
lean_object* v_fst_2101_; 
v_fst_2101_ = lean_ctor_get(v_____s_2100_, 0);
lean_inc(v_fst_2101_);
lean_dec_ref(v_____s_2100_);
if (lean_obj_tag(v_fst_2101_) == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_apply_2(v_toPure_2099_, lean_box(0), v___x_2102_);
return v___x_2103_;
}
else
{
lean_object* v_val_2104_; lean_object* v___x_2105_; 
v_val_2104_ = lean_ctor_get(v_fst_2101_, 0);
lean_inc(v_val_2104_);
lean_dec_ref(v_fst_2101_);
v___x_2105_ = lean_apply_2(v_toPure_2099_, lean_box(0), v_val_2104_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2106_, lean_object* v_toPure_2107_, lean_object* v_a_2108_, lean_object* v___x_2109_, uint8_t v_____do__lift_2110_){
_start:
{
if (v_____do__lift_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
lean_dec(v_a_2108_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2106_);
v___x_2112_ = lean_apply_2(v_toPure_2107_, lean_box(0), v___x_2111_);
return v___x_2112_;
}
else
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref(v___x_2106_);
v___x_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_a_2108_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2109_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
v___x_2117_ = lean_apply_2(v_toPure_2107_, lean_box(0), v___x_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2118_, lean_object* v_toPure_2119_, lean_object* v_a_2120_, lean_object* v___x_2121_, lean_object* v_____do__lift_2122_){
_start:
{
uint8_t v_____do__lift_124__boxed_2123_; lean_object* v_res_2124_; 
v_____do__lift_124__boxed_2123_ = lean_unbox(v_____do__lift_2122_);
v_res_2124_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2118_, v_toPure_2119_, v_a_2120_, v___x_2121_, v_____do__lift_124__boxed_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2125_, lean_object* v_toPure_2126_, lean_object* v___x_2127_, lean_object* v_f_2128_, lean_object* v_toBind_2129_, lean_object* v_a_2130_, lean_object* v_x_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_inc(v_a_2130_);
v___f_2133_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2133_, 0, v___x_2125_);
lean_closure_set(v___f_2133_, 1, v_toPure_2126_);
lean_closure_set(v___f_2133_, 2, v_a_2130_);
lean_closure_set(v___f_2133_, 3, v___x_2127_);
v___x_2134_ = lean_apply_1(v_f_2128_, v_a_2130_);
v___x_2135_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v___x_2134_, v___f_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2136_, lean_object* v_toPure_2137_, lean_object* v___x_2138_, lean_object* v_f_2139_, lean_object* v_toBind_2140_, lean_object* v_a_2141_, lean_object* v_x_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2136_, v_toPure_2137_, v___x_2138_, v_f_2139_, v_toBind_2140_, v_a_2141_, v_x_2142_, v___y_2143_);
lean_dec_ref(v___y_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2148_, lean_object* v_f_2149_, lean_object* v_as_2150_){
_start:
{
lean_object* v_toApplicative_2151_; lean_object* v_toBind_2152_; lean_object* v_toPure_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___f_2157_; size_t v_sz_2158_; size_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_toApplicative_2151_ = lean_ctor_get(v_inst_2148_, 0);
v_toBind_2152_ = lean_ctor_get(v_inst_2148_, 1);
lean_inc_n(v_toBind_2152_, 2);
v_toPure_2153_ = lean_ctor_get(v_toApplicative_2151_, 1);
v___x_2154_ = lean_box(0);
v___x_2155_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2153_, 2);
v___f_2156_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2156_, 0, v_toPure_2153_);
v___f_2157_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2157_, 0, v___x_2155_);
lean_closure_set(v___f_2157_, 1, v_toPure_2153_);
lean_closure_set(v___f_2157_, 2, v___x_2154_);
lean_closure_set(v___f_2157_, 3, v_f_2149_);
lean_closure_set(v___f_2157_, 4, v_toBind_2152_);
v_sz_2158_ = lean_array_size(v_as_2150_);
v___x_2159_ = ((size_t)0ULL);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2148_, v_as_2150_, v___f_2157_, v_sz_2158_, v___x_2159_, v___x_2155_);
v___x_2161_ = lean_apply_4(v_toBind_2152_, lean_box(0), lean_box(0), v___x_2160_, v___f_2156_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2162_, lean_object* v_00_u03b1_2163_, lean_object* v_m_2164_, lean_object* v_inst_2165_, lean_object* v_f_2166_, lean_object* v_as_2167_){
_start:
{
lean_object* v_toApplicative_2168_; lean_object* v_toBind_2169_; lean_object* v_toPure_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; lean_object* v___f_2174_; size_t v_sz_2175_; size_t v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_toApplicative_2168_ = lean_ctor_get(v_inst_2165_, 0);
v_toBind_2169_ = lean_ctor_get(v_inst_2165_, 1);
lean_inc_n(v_toBind_2169_, 2);
v_toPure_2170_ = lean_ctor_get(v_toApplicative_2168_, 1);
v___x_2171_ = lean_box(0);
v___x_2172_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2170_, 2);
v___f_2173_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2173_, 0, v_toPure_2170_);
v___f_2174_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2174_, 0, v___x_2172_);
lean_closure_set(v___f_2174_, 1, v_toPure_2170_);
lean_closure_set(v___f_2174_, 2, v___x_2171_);
lean_closure_set(v___f_2174_, 3, v_f_2166_);
lean_closure_set(v___f_2174_, 4, v_toBind_2169_);
v_sz_2175_ = lean_array_size(v_as_2167_);
v___x_2176_ = ((size_t)0ULL);
v___x_2177_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2165_, v_as_2167_, v___f_2174_, v_sz_2175_, v___x_2176_, v___x_2172_);
v___x_2178_ = lean_apply_4(v_toBind_2169_, lean_box(0), lean_box(0), v___x_2177_, v___f_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2179_, lean_object* v_00_u03b1_2180_, lean_object* v_m_2181_, lean_object* v_inst_2182_, lean_object* v_f_2183_, lean_object* v_as_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Vector_findM_x3f(v_n_2179_, v_00_u03b1_2180_, v_m_2181_, v_inst_2182_, v_f_2183_, v_as_2184_);
lean_dec(v_n_2179_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2186_, lean_object* v_toPure_2187_, lean_object* v___x_2188_, lean_object* v_____do__lift_2189_){
_start:
{
if (lean_obj_tag(v_____do__lift_2189_) == 1)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec_ref(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2190_, 0, v_____do__lift_2189_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2186_);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
v___x_2193_ = lean_apply_2(v_toPure_2187_, lean_box(0), v___x_2192_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v_____do__lift_2189_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2188_);
v___x_2195_ = lean_apply_2(v_toPure_2187_, lean_box(0), v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2196_, lean_object* v_toBind_2197_, lean_object* v___f_2198_, lean_object* v_a_2199_, lean_object* v_x_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_apply_1(v_f_2196_, v_a_2199_);
v___x_2203_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v___x_2202_, v___f_2198_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2204_, lean_object* v_toBind_2205_, lean_object* v___f_2206_, lean_object* v_a_2207_, lean_object* v_x_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2204_, v_toBind_2205_, v___f_2206_, v_a_2207_, v_x_2208_, v___y_2209_);
lean_dec_ref(v___y_2209_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2211_, lean_object* v_f_2212_, lean_object* v_as_2213_){
_start:
{
lean_object* v_toApplicative_2214_; lean_object* v_toBind_2215_; lean_object* v_toPure_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___f_2219_; lean_object* v___f_2220_; lean_object* v___f_2221_; size_t v_sz_2222_; size_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_toApplicative_2214_ = lean_ctor_get(v_inst_2211_, 0);
v_toBind_2215_ = lean_ctor_get(v_inst_2211_, 1);
lean_inc_n(v_toBind_2215_, 2);
v_toPure_2216_ = lean_ctor_get(v_toApplicative_2214_, 1);
v___x_2217_ = lean_box(0);
v___x_2218_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2216_, 2);
v___f_2219_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2219_, 0, v_toPure_2216_);
v___f_2220_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2220_, 0, v___x_2217_);
lean_closure_set(v___f_2220_, 1, v_toPure_2216_);
lean_closure_set(v___f_2220_, 2, v___x_2218_);
v___f_2221_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2221_, 0, v_f_2212_);
lean_closure_set(v___f_2221_, 1, v_toBind_2215_);
lean_closure_set(v___f_2221_, 2, v___f_2220_);
v_sz_2222_ = lean_array_size(v_as_2213_);
v___x_2223_ = ((size_t)0ULL);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2211_, v_as_2213_, v___f_2221_, v_sz_2222_, v___x_2223_, v___x_2218_);
v___x_2225_ = lean_apply_4(v_toBind_2215_, lean_box(0), lean_box(0), v___x_2224_, v___f_2219_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2226_, lean_object* v_00_u03b1_2227_, lean_object* v_00_u03b2_2228_, lean_object* v_n_2229_, lean_object* v_inst_2230_, lean_object* v_f_2231_, lean_object* v_as_2232_){
_start:
{
lean_object* v_toApplicative_2233_; lean_object* v_toBind_2234_; lean_object* v_toPure_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___f_2240_; size_t v_sz_2241_; size_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_toApplicative_2233_ = lean_ctor_get(v_inst_2230_, 0);
v_toBind_2234_ = lean_ctor_get(v_inst_2230_, 1);
lean_inc_n(v_toBind_2234_, 2);
v_toPure_2235_ = lean_ctor_get(v_toApplicative_2233_, 1);
v___x_2236_ = lean_box(0);
v___x_2237_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2235_, 2);
v___f_2238_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2238_, 0, v_toPure_2235_);
v___f_2239_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2239_, 0, v___x_2236_);
lean_closure_set(v___f_2239_, 1, v_toPure_2235_);
lean_closure_set(v___f_2239_, 2, v___x_2237_);
v___f_2240_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2240_, 0, v_f_2231_);
lean_closure_set(v___f_2240_, 1, v_toBind_2234_);
lean_closure_set(v___f_2240_, 2, v___f_2239_);
v_sz_2241_ = lean_array_size(v_as_2232_);
v___x_2242_ = ((size_t)0ULL);
v___x_2243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2230_, v_as_2232_, v___f_2240_, v_sz_2241_, v___x_2242_, v___x_2237_);
v___x_2244_ = lean_apply_4(v_toBind_2234_, lean_box(0), lean_box(0), v___x_2243_, v___f_2238_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2245_, lean_object* v_00_u03b1_2246_, lean_object* v_00_u03b2_2247_, lean_object* v_n_2248_, lean_object* v_inst_2249_, lean_object* v_f_2250_, lean_object* v_as_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Vector_findSomeM_x3f(v_m_2245_, v_00_u03b1_2246_, v_00_u03b2_2247_, v_n_2248_, v_inst_2249_, v_f_2250_, v_as_2251_);
lean_dec(v_n_2248_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2253_, lean_object* v_a_2254_, uint8_t v_____do__lift_2255_){
_start:
{
if (v_____do__lift_2255_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec(v_a_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_apply_2(v_toPure_2253_, lean_box(0), v___x_2256_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v_a_2254_);
v___x_2259_ = lean_apply_2(v_toPure_2253_, lean_box(0), v___x_2258_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2260_, lean_object* v_a_2261_, lean_object* v_____do__lift_2262_){
_start:
{
uint8_t v_____do__lift_50__boxed_2263_; lean_object* v_res_2264_; 
v_____do__lift_50__boxed_2263_ = lean_unbox(v_____do__lift_2262_);
v_res_2264_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2260_, v_a_2261_, v_____do__lift_50__boxed_2263_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2265_, lean_object* v_f_2266_, lean_object* v_toBind_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v___f_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_inc(v_a_2268_);
v___f_2269_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2269_, 0, v_toPure_2265_);
lean_closure_set(v___f_2269_, 1, v_a_2268_);
v___x_2270_ = lean_apply_1(v_f_2266_, v_a_2268_);
v___x_2271_ = lean_apply_4(v_toBind_2267_, lean_box(0), lean_box(0), v___x_2270_, v___f_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2272_, lean_object* v_f_2273_, lean_object* v_as_2274_){
_start:
{
lean_object* v_toApplicative_2275_; lean_object* v_toBind_2276_; lean_object* v_toPure_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v_toApplicative_2275_ = lean_ctor_get(v_inst_2272_, 0);
v_toBind_2276_ = lean_ctor_get(v_inst_2272_, 1);
v_toPure_2277_ = lean_ctor_get(v_toApplicative_2275_, 1);
lean_inc(v_toBind_2276_);
lean_inc(v_toPure_2277_);
v___f_2278_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2278_, 0, v_toPure_2277_);
lean_closure_set(v___f_2278_, 1, v_f_2273_);
lean_closure_set(v___f_2278_, 2, v_toBind_2276_);
v___x_2279_ = lean_array_get_size(v_as_2274_);
v___x_2280_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2272_, v___f_2278_, v_as_2274_, v___x_2279_, lean_box(0));
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2281_, lean_object* v_00_u03b1_2282_, lean_object* v_m_2283_, lean_object* v_inst_2284_, lean_object* v_f_2285_, lean_object* v_as_2286_){
_start:
{
lean_object* v_toApplicative_2287_; lean_object* v_toBind_2288_; lean_object* v_toPure_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_toApplicative_2287_ = lean_ctor_get(v_inst_2284_, 0);
v_toBind_2288_ = lean_ctor_get(v_inst_2284_, 1);
v_toPure_2289_ = lean_ctor_get(v_toApplicative_2287_, 1);
lean_inc(v_toBind_2288_);
lean_inc(v_toPure_2289_);
v___f_2290_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2290_, 0, v_toPure_2289_);
lean_closure_set(v___f_2290_, 1, v_f_2285_);
lean_closure_set(v___f_2290_, 2, v_toBind_2288_);
v___x_2291_ = lean_array_get_size(v_as_2286_);
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2284_, v___f_2290_, v_as_2286_, v___x_2291_, lean_box(0));
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2293_, lean_object* v_00_u03b1_2294_, lean_object* v_m_2295_, lean_object* v_inst_2296_, lean_object* v_f_2297_, lean_object* v_as_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Vector_findRevM_x3f(v_n_2293_, v_00_u03b1_2294_, v_m_2295_, v_inst_2296_, v_f_2297_, v_as_2298_);
lean_dec(v_n_2293_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2300_, lean_object* v_f_2301_, lean_object* v_as_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_array_get_size(v_as_2302_);
v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2300_, v_f_2301_, v_as_2302_, v___x_2303_, lean_box(0));
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2305_, lean_object* v_00_u03b1_2306_, lean_object* v_00_u03b2_2307_, lean_object* v_n_2308_, lean_object* v_inst_2309_, lean_object* v_f_2310_, lean_object* v_as_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_array_get_size(v_as_2311_);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2309_, v_f_2310_, v_as_2311_, v___x_2312_, lean_box(0));
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2314_, lean_object* v_00_u03b1_2315_, lean_object* v_00_u03b2_2316_, lean_object* v_n_2317_, lean_object* v_inst_2318_, lean_object* v_f_2319_, lean_object* v_as_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Vector_findSomeRevM_x3f(v_m_2314_, v_00_u03b1_2315_, v_00_u03b2_2316_, v_n_2317_, v_inst_2318_, v_f_2319_, v_as_2320_);
lean_dec(v_n_2317_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2322_, lean_object* v___x_2323_, lean_object* v___x_2324_, lean_object* v_a_2325_, lean_object* v_x_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
lean_inc(v_a_2325_);
v___x_2328_ = lean_apply_1(v_f_2322_, v_a_2325_);
v___x_2329_ = lean_unbox(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; 
lean_dec(v_a_2325_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2323_);
return v___x_2330_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v___x_2323_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2325_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_2324_);
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2335_, lean_object* v___x_2336_, lean_object* v___x_2337_, lean_object* v_a_2338_, lean_object* v_x_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Vector_find_x3f___redArg___lam__0(v_f_2335_, v___x_2336_, v___x_2337_, v_a_2338_, v_x_2339_, v___y_2340_);
lean_dec_ref(v___y_2340_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2342_, lean_object* v_as_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___f_2348_; size_t v_sz_2349_; size_t v___x_2350_; lean_object* v___x_2351_; lean_object* v_fst_2352_; 
v___x_2344_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2345_ = lean_box(0);
v___x_2346_ = lean_box(0);
v___x_2347_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2348_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2348_, 0, v_f_2342_);
lean_closure_set(v___f_2348_, 1, v___x_2347_);
lean_closure_set(v___f_2348_, 2, v___x_2346_);
v_sz_2349_ = lean_array_size(v_as_2343_);
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2344_, v_as_2343_, v___f_2348_, v_sz_2349_, v___x_2350_, v___x_2347_);
v_fst_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_fst_2352_);
lean_dec(v___x_2351_);
if (lean_obj_tag(v_fst_2352_) == 0)
{
return v___x_2345_;
}
else
{
lean_object* v_val_2353_; 
v_val_2353_ = lean_ctor_get(v_fst_2352_, 0);
lean_inc(v_val_2353_);
lean_dec_ref(v_fst_2352_);
return v_val_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2354_, lean_object* v_00_u03b1_2355_, lean_object* v_f_2356_, lean_object* v_as_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___f_2362_; size_t v_sz_2363_; size_t v___x_2364_; lean_object* v___x_2365_; lean_object* v_fst_2366_; 
v___x_2358_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_box(0);
v___x_2361_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2362_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2362_, 0, v_f_2356_);
lean_closure_set(v___f_2362_, 1, v___x_2361_);
lean_closure_set(v___f_2362_, 2, v___x_2360_);
v_sz_2363_ = lean_array_size(v_as_2357_);
v___x_2364_ = ((size_t)0ULL);
v___x_2365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2358_, v_as_2357_, v___f_2362_, v_sz_2363_, v___x_2364_, v___x_2361_);
v_fst_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_fst_2366_);
lean_dec(v___x_2365_);
if (lean_obj_tag(v_fst_2366_) == 0)
{
return v___x_2359_;
}
else
{
lean_object* v_val_2367_; 
v_val_2367_ = lean_ctor_get(v_fst_2366_, 0);
lean_inc(v_val_2367_);
lean_dec_ref(v_fst_2366_);
return v_val_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2368_, lean_object* v_00_u03b1_2369_, lean_object* v_f_2370_, lean_object* v_as_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Vector_find_x3f(v_n_2368_, v_00_u03b1_2369_, v_f_2370_, v_as_2371_);
lean_dec(v_n_2368_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2375_; uint8_t v___x_2376_; 
lean_inc(v_a_2374_);
v___x_2375_ = lean_apply_1(v_f_2373_, v_a_2374_);
v___x_2376_ = lean_unbox(v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; 
lean_dec(v_a_2374_);
v___x_2377_ = lean_box(0);
return v___x_2377_;
}
else
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2374_);
return v___x_2378_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2379_, lean_object* v_as_2380_){
_start:
{
lean_object* v___f_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___f_2381_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2381_, 0, v_f_2379_);
v___x_2382_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2383_ = lean_array_get_size(v_as_2380_);
v___x_2384_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2382_, v___f_2381_, v_as_2380_, v___x_2383_, lean_box(0));
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2385_, lean_object* v_00_u03b1_2386_, lean_object* v_f_2387_, lean_object* v_as_2388_){
_start:
{
lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___f_2389_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2389_, 0, v_f_2387_);
v___x_2390_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2391_ = lean_array_get_size(v_as_2388_);
v___x_2392_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2390_, v___f_2389_, v_as_2388_, v___x_2391_, lean_box(0));
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2393_, lean_object* v_00_u03b1_2394_, lean_object* v_f_2395_, lean_object* v_as_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_Vector_findRev_x3f(v_n_2393_, v_00_u03b1_2394_, v_f_2395_, v_as_2396_);
lean_dec(v_n_2393_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2398_, lean_object* v___x_2399_, lean_object* v___x_2400_, lean_object* v_a_2401_, lean_object* v_x_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_apply_1(v_f_2398_, v_a_2401_);
if (lean_obj_tag(v___x_2404_) == 1)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec_ref(v___x_2400_);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2399_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; 
lean_dec(v___x_2404_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2400_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2409_, lean_object* v___x_2410_, lean_object* v___x_2411_, lean_object* v_a_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2409_, v___x_2410_, v___x_2411_, v_a_2412_, v_x_2413_, v___y_2414_);
lean_dec_ref(v___y_2414_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2416_, lean_object* v_as_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; size_t v_sz_2423_; size_t v___x_2424_; lean_object* v___x_2425_; lean_object* v_fst_2426_; 
v___x_2418_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2419_ = lean_box(0);
v___x_2420_ = lean_box(0);
v___x_2421_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2422_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2422_, 0, v_f_2416_);
lean_closure_set(v___f_2422_, 1, v___x_2420_);
lean_closure_set(v___f_2422_, 2, v___x_2421_);
v_sz_2423_ = lean_array_size(v_as_2417_);
v___x_2424_ = ((size_t)0ULL);
v___x_2425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2418_, v_as_2417_, v___f_2422_, v_sz_2423_, v___x_2424_, v___x_2421_);
v_fst_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_fst_2426_);
lean_dec(v___x_2425_);
if (lean_obj_tag(v_fst_2426_) == 0)
{
return v___x_2419_;
}
else
{
lean_object* v_val_2427_; 
v_val_2427_ = lean_ctor_get(v_fst_2426_, 0);
lean_inc(v_val_2427_);
lean_dec_ref(v_fst_2426_);
return v_val_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_n_2430_, lean_object* v_f_2431_, lean_object* v_as_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___f_2437_; size_t v_sz_2438_; size_t v___x_2439_; lean_object* v___x_2440_; lean_object* v_fst_2441_; 
v___x_2433_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2434_ = lean_box(0);
v___x_2435_ = lean_box(0);
v___x_2436_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2437_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2437_, 0, v_f_2431_);
lean_closure_set(v___f_2437_, 1, v___x_2435_);
lean_closure_set(v___f_2437_, 2, v___x_2436_);
v_sz_2438_ = lean_array_size(v_as_2432_);
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2433_, v_as_2432_, v___f_2437_, v_sz_2438_, v___x_2439_, v___x_2436_);
v_fst_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_fst_2441_);
lean_dec(v___x_2440_);
if (lean_obj_tag(v_fst_2441_) == 0)
{
return v___x_2434_;
}
else
{
lean_object* v_val_2442_; 
v_val_2442_ = lean_ctor_get(v_fst_2441_, 0);
lean_inc(v_val_2442_);
lean_dec_ref(v_fst_2441_);
return v_val_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2443_, lean_object* v_00_u03b2_2444_, lean_object* v_n_2445_, lean_object* v_f_2446_, lean_object* v_as_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Vector_findSome_x3f(v_00_u03b1_2443_, v_00_u03b2_2444_, v_n_2445_, v_f_2446_, v_as_2447_);
lean_dec(v_n_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2449_, lean_object* v_x_2450_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_apply_1(v_f_2449_, v_x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2452_, lean_object* v_as_2453_){
_start:
{
lean_object* v___f_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___f_2454_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2454_, 0, v_f_2452_);
v___x_2455_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2456_ = lean_array_get_size(v_as_2453_);
v___x_2457_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2455_, v___f_2454_, v_as_2453_, v___x_2456_, lean_box(0));
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2458_, lean_object* v_00_u03b2_2459_, lean_object* v_n_2460_, lean_object* v_f_2461_, lean_object* v_as_2462_){
_start:
{
lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___f_2463_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2463_, 0, v_f_2461_);
v___x_2464_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2465_ = lean_array_get_size(v_as_2462_);
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2464_, v___f_2463_, v_as_2462_, v___x_2465_, lean_box(0));
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2467_, lean_object* v_00_u03b2_2468_, lean_object* v_n_2469_, lean_object* v_f_2470_, lean_object* v_as_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2467_, v_00_u03b2_2468_, v_n_2469_, v_f_2470_, v_as_2471_);
lean_dec(v_n_2469_);
return v_res_2472_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2473_, lean_object* v_xs_2474_, lean_object* v_ys_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = l_Array_isPrefixOf___redArg(v_inst_2473_, v_xs_2474_, v_ys_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2477_, lean_object* v_xs_2478_, lean_object* v_ys_2479_){
_start:
{
uint8_t v_res_2480_; lean_object* v_r_2481_; 
v_res_2480_ = l_Vector_isPrefixOf___redArg(v_inst_2477_, v_xs_2478_, v_ys_2479_);
lean_dec_ref(v_ys_2479_);
lean_dec_ref(v_xs_2478_);
v_r_2481_ = lean_box(v_res_2480_);
return v_r_2481_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2482_, lean_object* v_m_2483_, lean_object* v_n_2484_, lean_object* v_inst_2485_, lean_object* v_xs_2486_, lean_object* v_ys_2487_){
_start:
{
uint8_t v___x_2488_; 
v___x_2488_ = l_Array_isPrefixOf___redArg(v_inst_2485_, v_xs_2486_, v_ys_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_m_2490_, lean_object* v_n_2491_, lean_object* v_inst_2492_, lean_object* v_xs_2493_, lean_object* v_ys_2494_){
_start:
{
uint8_t v_res_2495_; lean_object* v_r_2496_; 
v_res_2495_ = l_Vector_isPrefixOf(v_00_u03b1_2489_, v_m_2490_, v_n_2491_, v_inst_2492_, v_xs_2493_, v_ys_2494_);
lean_dec_ref(v_ys_2494_);
lean_dec_ref(v_xs_2493_);
lean_dec(v_n_2491_);
lean_dec(v_m_2490_);
v_r_2496_ = lean_box(v_res_2495_);
return v_r_2496_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2497_, lean_object* v_p_2498_, lean_object* v_xs_2499_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_array_get_size(v_xs_2499_);
v___x_2502_ = lean_nat_dec_lt(v___x_2500_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v_toApplicative_2503_; lean_object* v_toPure_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v_xs_2499_);
lean_dec(v_p_2498_);
v_toApplicative_2503_ = lean_ctor_get(v_inst_2497_, 0);
lean_inc_ref(v_toApplicative_2503_);
lean_dec_ref(v_inst_2497_);
v_toPure_2504_ = lean_ctor_get(v_toApplicative_2503_, 1);
lean_inc(v_toPure_2504_);
lean_dec_ref(v_toApplicative_2503_);
v___x_2505_ = lean_box(v___x_2502_);
v___x_2506_ = lean_apply_2(v_toPure_2504_, lean_box(0), v___x_2505_);
return v___x_2506_;
}
else
{
if (v___x_2502_ == 0)
{
lean_object* v_toApplicative_2507_; lean_object* v_toPure_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec_ref(v_xs_2499_);
lean_dec(v_p_2498_);
v_toApplicative_2507_ = lean_ctor_get(v_inst_2497_, 0);
lean_inc_ref(v_toApplicative_2507_);
lean_dec_ref(v_inst_2497_);
v_toPure_2508_ = lean_ctor_get(v_toApplicative_2507_, 1);
lean_inc(v_toPure_2508_);
lean_dec_ref(v_toApplicative_2507_);
v___x_2509_ = lean_box(v___x_2502_);
v___x_2510_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2509_);
return v___x_2510_;
}
else
{
size_t v___x_2511_; size_t v___x_2512_; lean_object* v___x_2513_; 
v___x_2511_ = ((size_t)0ULL);
v___x_2512_ = lean_usize_of_nat(v___x_2501_);
v___x_2513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2497_, v_p_2498_, v_xs_2499_, v___x_2511_, v___x_2512_);
return v___x_2513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2514_, lean_object* v_00_u03b1_2515_, lean_object* v_n_2516_, lean_object* v_inst_2517_, lean_object* v_p_2518_, lean_object* v_xs_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_xs_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v_toApplicative_2523_; lean_object* v_toPure_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_xs_2519_);
lean_dec(v_p_2518_);
v_toApplicative_2523_ = lean_ctor_get(v_inst_2517_, 0);
lean_inc_ref(v_toApplicative_2523_);
lean_dec_ref(v_inst_2517_);
v_toPure_2524_ = lean_ctor_get(v_toApplicative_2523_, 1);
lean_inc(v_toPure_2524_);
lean_dec_ref(v_toApplicative_2523_);
v___x_2525_ = lean_box(v___x_2522_);
v___x_2526_ = lean_apply_2(v_toPure_2524_, lean_box(0), v___x_2525_);
return v___x_2526_;
}
else
{
if (v___x_2522_ == 0)
{
lean_object* v_toApplicative_2527_; lean_object* v_toPure_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec_ref(v_xs_2519_);
lean_dec(v_p_2518_);
v_toApplicative_2527_ = lean_ctor_get(v_inst_2517_, 0);
lean_inc_ref(v_toApplicative_2527_);
lean_dec_ref(v_inst_2517_);
v_toPure_2528_ = lean_ctor_get(v_toApplicative_2527_, 1);
lean_inc(v_toPure_2528_);
lean_dec_ref(v_toApplicative_2527_);
v___x_2529_ = lean_box(v___x_2522_);
v___x_2530_ = lean_apply_2(v_toPure_2528_, lean_box(0), v___x_2529_);
return v___x_2530_;
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = lean_usize_of_nat(v___x_2521_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2517_, v_p_2518_, v_xs_2519_, v___x_2531_, v___x_2532_);
return v___x_2533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2534_, lean_object* v_00_u03b1_2535_, lean_object* v_n_2536_, lean_object* v_inst_2537_, lean_object* v_p_2538_, lean_object* v_xs_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Vector_anyM(v_m_2534_, v_00_u03b1_2535_, v_n_2536_, v_inst_2537_, v_p_2538_, v_xs_2539_);
lean_dec(v_n_2536_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2541_, uint8_t v_____do__lift_2542_){
_start:
{
if (v_____do__lift_2542_ == 0)
{
uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = 1;
v___x_2544_ = lean_box(v___x_2543_);
v___x_2545_ = lean_apply_2(v_toPure_2541_, lean_box(0), v___x_2544_);
return v___x_2545_;
}
else
{
uint8_t v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = 0;
v___x_2547_ = lean_box(v___x_2546_);
v___x_2548_ = lean_apply_2(v_toPure_2541_, lean_box(0), v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2549_, lean_object* v_____do__lift_2550_){
_start:
{
uint8_t v_____do__lift_117__boxed_2551_; lean_object* v_res_2552_; 
v_____do__lift_117__boxed_2551_ = lean_unbox(v_____do__lift_2550_);
v_res_2552_ = l_Vector_allM___redArg___lam__0(v_toPure_2549_, v_____do__lift_117__boxed_2551_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2553_, uint8_t v___x_2554_, uint8_t v_____do__lift_2555_){
_start:
{
if (v_____do__lift_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_box(v___x_2554_);
v___x_2557_ = lean_apply_2(v_toPure_2553_, lean_box(0), v___x_2556_);
return v___x_2557_;
}
else
{
uint8_t v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = 0;
v___x_2559_ = lean_box(v___x_2558_);
v___x_2560_ = lean_apply_2(v_toPure_2553_, lean_box(0), v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2561_, lean_object* v___x_2562_, lean_object* v_____do__lift_2563_){
_start:
{
uint8_t v___x_132__boxed_2564_; uint8_t v_____do__lift_133__boxed_2565_; lean_object* v_res_2566_; 
v___x_132__boxed_2564_ = lean_unbox(v___x_2562_);
v_____do__lift_133__boxed_2565_ = lean_unbox(v_____do__lift_2563_);
v_res_2566_ = l_Vector_allM___redArg___lam__1(v_toPure_2561_, v___x_132__boxed_2564_, v_____do__lift_133__boxed_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2567_, lean_object* v_toBind_2568_, lean_object* v___f_2569_, lean_object* v_v_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_apply_1(v_p_2567_, v_v_2570_);
v___x_2572_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2571_, v___f_2569_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2573_, lean_object* v_p_2574_, lean_object* v_xs_2575_){
_start:
{
lean_object* v_toApplicative_2576_; lean_object* v_toBind_2577_; lean_object* v_toPure_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; uint8_t v___x_2582_; 
v_toApplicative_2576_ = lean_ctor_get(v_inst_2573_, 0);
v_toBind_2577_ = lean_ctor_get(v_inst_2573_, 1);
lean_inc(v_toBind_2577_);
v_toPure_2578_ = lean_ctor_get(v_toApplicative_2576_, 1);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_array_get_size(v_xs_2575_);
lean_inc(v_toPure_2578_);
v___f_2581_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2581_, 0, v_toPure_2578_);
v___x_2582_ = lean_nat_dec_lt(v___x_2579_, v___x_2580_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
lean_inc(v_toPure_2578_);
lean_dec_ref(v_xs_2575_);
lean_dec(v_p_2574_);
lean_dec_ref(v_inst_2573_);
v___x_2583_ = lean_box(v___x_2582_);
v___x_2584_ = lean_apply_2(v_toPure_2578_, lean_box(0), v___x_2583_);
v___x_2585_ = lean_apply_4(v_toBind_2577_, lean_box(0), lean_box(0), v___x_2584_, v___f_2581_);
return v___x_2585_;
}
else
{
if (v___x_2582_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
lean_inc(v_toPure_2578_);
lean_dec_ref(v_xs_2575_);
lean_dec(v_p_2574_);
lean_dec_ref(v_inst_2573_);
v___x_2586_ = lean_box(v___x_2582_);
v___x_2587_ = lean_apply_2(v_toPure_2578_, lean_box(0), v___x_2586_);
v___x_2588_ = lean_apply_4(v_toBind_2577_, lean_box(0), lean_box(0), v___x_2587_, v___f_2581_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2589_ = lean_box(v___x_2582_);
lean_inc(v_toPure_2578_);
v___f_2590_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2590_, 0, v_toPure_2578_);
lean_closure_set(v___f_2590_, 1, v___x_2589_);
lean_inc(v_toBind_2577_);
v___f_2591_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2591_, 0, v_p_2574_);
lean_closure_set(v___f_2591_, 1, v_toBind_2577_);
lean_closure_set(v___f_2591_, 2, v___f_2590_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = lean_usize_of_nat(v___x_2580_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2573_, v___f_2591_, v_xs_2575_, v___x_2592_, v___x_2593_);
v___x_2595_ = lean_apply_4(v_toBind_2577_, lean_box(0), lean_box(0), v___x_2594_, v___f_2581_);
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2596_, lean_object* v_00_u03b1_2597_, lean_object* v_n_2598_, lean_object* v_inst_2599_, lean_object* v_p_2600_, lean_object* v_xs_2601_){
_start:
{
lean_object* v_toApplicative_2602_; lean_object* v_toBind_2603_; lean_object* v_toPure_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; uint8_t v___x_2608_; 
v_toApplicative_2602_ = lean_ctor_get(v_inst_2599_, 0);
v_toBind_2603_ = lean_ctor_get(v_inst_2599_, 1);
lean_inc(v_toBind_2603_);
v_toPure_2604_ = lean_ctor_get(v_toApplicative_2602_, 1);
v___x_2605_ = lean_unsigned_to_nat(0u);
v___x_2606_ = lean_array_get_size(v_xs_2601_);
lean_inc(v_toPure_2604_);
v___f_2607_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2607_, 0, v_toPure_2604_);
v___x_2608_ = lean_nat_dec_lt(v___x_2605_, v___x_2606_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_inc(v_toPure_2604_);
lean_dec_ref(v_xs_2601_);
lean_dec(v_p_2600_);
lean_dec_ref(v_inst_2599_);
v___x_2609_ = lean_box(v___x_2608_);
v___x_2610_ = lean_apply_2(v_toPure_2604_, lean_box(0), v___x_2609_);
v___x_2611_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v___x_2610_, v___f_2607_);
return v___x_2611_;
}
else
{
if (v___x_2608_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_inc(v_toPure_2604_);
lean_dec_ref(v_xs_2601_);
lean_dec(v_p_2600_);
lean_dec_ref(v_inst_2599_);
v___x_2612_ = lean_box(v___x_2608_);
v___x_2613_ = lean_apply_2(v_toPure_2604_, lean_box(0), v___x_2612_);
v___x_2614_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v___x_2613_, v___f_2607_);
return v___x_2614_;
}
else
{
lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; size_t v___x_2618_; size_t v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2615_ = lean_box(v___x_2608_);
lean_inc(v_toPure_2604_);
v___f_2616_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2616_, 0, v_toPure_2604_);
lean_closure_set(v___f_2616_, 1, v___x_2615_);
lean_inc(v_toBind_2603_);
v___f_2617_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2617_, 0, v_p_2600_);
lean_closure_set(v___f_2617_, 1, v_toBind_2603_);
lean_closure_set(v___f_2617_, 2, v___f_2616_);
v___x_2618_ = ((size_t)0ULL);
v___x_2619_ = lean_usize_of_nat(v___x_2606_);
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2599_, v___f_2617_, v_xs_2601_, v___x_2618_, v___x_2619_);
v___x_2621_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v___x_2620_, v___f_2607_);
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2622_, lean_object* v_00_u03b1_2623_, lean_object* v_n_2624_, lean_object* v_inst_2625_, lean_object* v_p_2626_, lean_object* v_xs_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Vector_allM(v_m_2622_, v_00_u03b1_2623_, v_n_2624_, v_inst_2625_, v_p_2626_, v_xs_2627_);
lean_dec(v_n_2624_);
return v_res_2628_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2629_, lean_object* v_x_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = lean_apply_1(v_p_2629_, v_x_2630_);
v___x_2632_ = lean_unbox(v___x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2633_, lean_object* v_x_2634_){
_start:
{
uint8_t v_res_2635_; lean_object* v_r_2636_; 
v_res_2635_ = l_Vector_any___redArg___lam__0(v_p_2633_, v_x_2634_);
v_r_2636_ = lean_box(v_res_2635_);
return v_r_2636_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2637_, lean_object* v_p_2638_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_array_get_size(v_xs_2637_);
v___x_2641_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2642_ = lean_nat_dec_lt(v___x_2639_, v___x_2640_);
if (v___x_2642_ == 0)
{
lean_dec_ref(v_p_2638_);
lean_dec_ref(v_xs_2637_);
return v___x_2642_;
}
else
{
if (v___x_2642_ == 0)
{
lean_dec_ref(v_p_2638_);
lean_dec_ref(v_xs_2637_);
return v___x_2642_;
}
else
{
lean_object* v___f_2643_; size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___f_2643_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2643_, 0, v_p_2638_);
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2640_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2641_, v___f_2643_, v_xs_2637_, v___x_2644_, v___x_2645_);
v___x_2647_ = lean_unbox(v___x_2646_);
lean_dec(v___x_2646_);
return v___x_2647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2648_, lean_object* v_p_2649_){
_start:
{
uint8_t v_res_2650_; lean_object* v_r_2651_; 
v_res_2650_ = l_Vector_any___redArg(v_xs_2648_, v_p_2649_);
v_r_2651_ = lean_box(v_res_2650_);
return v_r_2651_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2652_, lean_object* v_n_2653_, lean_object* v_xs_2654_, lean_object* v_p_2655_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2656_ = lean_unsigned_to_nat(0u);
v___x_2657_ = lean_array_get_size(v_xs_2654_);
v___x_2658_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2659_ = lean_nat_dec_lt(v___x_2656_, v___x_2657_);
if (v___x_2659_ == 0)
{
lean_dec_ref(v_p_2655_);
lean_dec_ref(v_xs_2654_);
return v___x_2659_;
}
else
{
if (v___x_2659_ == 0)
{
lean_dec_ref(v_p_2655_);
lean_dec_ref(v_xs_2654_);
return v___x_2659_;
}
else
{
lean_object* v___f_2660_; size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___f_2660_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2660_, 0, v_p_2655_);
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2657_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2658_, v___f_2660_, v_xs_2654_, v___x_2661_, v___x_2662_);
v___x_2664_ = lean_unbox(v___x_2663_);
lean_dec(v___x_2663_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2665_, lean_object* v_n_2666_, lean_object* v_xs_2667_, lean_object* v_p_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Vector_any(v_00_u03b1_2665_, v_n_2666_, v_xs_2667_, v_p_2668_);
lean_dec(v_n_2666_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2671_, uint8_t v___x_2672_, lean_object* v_v_2673_){
_start:
{
lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2674_ = lean_apply_1(v_p_2671_, v_v_2673_);
v___x_2675_ = lean_unbox(v___x_2674_);
if (v___x_2675_ == 0)
{
return v___x_2672_;
}
else
{
uint8_t v___x_2676_; 
v___x_2676_ = 0;
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2677_, lean_object* v___x_2678_, lean_object* v_v_2679_){
_start:
{
uint8_t v___x_79__boxed_2680_; uint8_t v_res_2681_; lean_object* v_r_2682_; 
v___x_79__boxed_2680_ = lean_unbox(v___x_2678_);
v_res_2681_ = l_Vector_all___redArg___lam__0(v_p_2677_, v___x_79__boxed_2680_, v_v_2679_);
v_r_2682_ = lean_box(v_res_2681_);
return v_r_2682_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2683_, lean_object* v_p_2684_){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_array_get_size(v_xs_2683_);
v___x_2687_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2688_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2688_ == 0)
{
uint8_t v___x_2689_; 
lean_dec_ref(v_p_2684_);
lean_dec_ref(v_xs_2683_);
v___x_2689_ = 1;
return v___x_2689_;
}
else
{
if (v___x_2688_ == 0)
{
lean_dec_ref(v_p_2684_);
lean_dec_ref(v_xs_2683_);
return v___x_2688_;
}
else
{
lean_object* v___x_2690_; lean_object* v___f_2691_; size_t v___x_2692_; size_t v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2690_ = lean_box(v___x_2688_);
v___f_2691_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2691_, 0, v_p_2684_);
lean_closure_set(v___f_2691_, 1, v___x_2690_);
v___x_2692_ = ((size_t)0ULL);
v___x_2693_ = lean_usize_of_nat(v___x_2686_);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2687_, v___f_2691_, v_xs_2683_, v___x_2692_, v___x_2693_);
v___x_2695_ = lean_unbox(v___x_2694_);
lean_dec(v___x_2694_);
if (v___x_2695_ == 0)
{
return v___x_2688_;
}
else
{
uint8_t v___x_2696_; 
v___x_2696_ = 0;
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2697_, lean_object* v_p_2698_){
_start:
{
uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_res_2699_ = l_Vector_all___redArg(v_xs_2697_, v_p_2698_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2701_, lean_object* v_n_2702_, lean_object* v_xs_2703_, lean_object* v_p_2704_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v_xs_2703_);
v___x_2707_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2708_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2708_ == 0)
{
uint8_t v___x_2709_; 
lean_dec_ref(v_p_2704_);
lean_dec_ref(v_xs_2703_);
v___x_2709_ = 1;
return v___x_2709_;
}
else
{
if (v___x_2708_ == 0)
{
lean_dec_ref(v_p_2704_);
lean_dec_ref(v_xs_2703_);
return v___x_2708_;
}
else
{
lean_object* v___x_2710_; lean_object* v___f_2711_; size_t v___x_2712_; size_t v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2710_ = lean_box(v___x_2708_);
v___f_2711_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2711_, 0, v_p_2704_);
lean_closure_set(v___f_2711_, 1, v___x_2710_);
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = lean_usize_of_nat(v___x_2706_);
v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2707_, v___f_2711_, v_xs_2703_, v___x_2712_, v___x_2713_);
v___x_2715_ = lean_unbox(v___x_2714_);
lean_dec(v___x_2714_);
if (v___x_2715_ == 0)
{
return v___x_2708_;
}
else
{
uint8_t v___x_2716_; 
v___x_2716_ = 0;
return v___x_2716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2717_, lean_object* v_n_2718_, lean_object* v_xs_2719_, lean_object* v_p_2720_){
_start:
{
uint8_t v_res_2721_; lean_object* v_r_2722_; 
v_res_2721_ = l_Vector_all(v_00_u03b1_2717_, v_n_2718_, v_xs_2719_, v_p_2720_);
lean_dec(v_n_2718_);
v_r_2722_ = lean_box(v_res_2721_);
return v_r_2722_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2723_, lean_object* v_x1_2724_, lean_object* v_x2_2725_){
_start:
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2726_ = lean_apply_1(v_p_2723_, v_x1_2724_);
v___x_2727_ = lean_unbox(v___x_2726_);
if (v___x_2727_ == 0)
{
lean_inc(v_x2_2725_);
return v_x2_2725_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_add(v_x2_2725_, v___x_2728_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2730_, lean_object* v_x1_2731_, lean_object* v_x2_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Vector_countP___redArg___lam__0(v_p_2730_, v_x1_2731_, v_x2_2732_);
lean_dec(v_x2_2732_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2734_, lean_object* v_xs_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = lean_array_get_size(v_xs_2735_);
v___x_2738_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2739_ = lean_nat_dec_lt(v___x_2736_, v___x_2737_);
if (v___x_2739_ == 0)
{
lean_dec_ref(v_xs_2735_);
lean_dec_ref(v_p_2734_);
return v___x_2736_;
}
else
{
lean_object* v___f_2740_; size_t v___x_2741_; size_t v___x_2742_; lean_object* v___x_2743_; 
v___f_2740_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2740_, 0, v_p_2734_);
v___x_2741_ = lean_usize_of_nat(v___x_2737_);
v___x_2742_ = ((size_t)0ULL);
v___x_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2738_, v___f_2740_, v_xs_2735_, v___x_2741_, v___x_2742_, v___x_2736_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2744_, lean_object* v_n_2745_, lean_object* v_p_2746_, lean_object* v_xs_2747_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_array_get_size(v_xs_2747_);
v___x_2750_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2751_ = lean_nat_dec_lt(v___x_2748_, v___x_2749_);
if (v___x_2751_ == 0)
{
lean_dec_ref(v_xs_2747_);
lean_dec_ref(v_p_2746_);
return v___x_2748_;
}
else
{
lean_object* v___f_2752_; size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___f_2752_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2752_, 0, v_p_2746_);
v___x_2753_ = lean_usize_of_nat(v___x_2749_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2750_, v___f_2752_, v_xs_2747_, v___x_2753_, v___x_2754_, v___x_2748_);
return v___x_2755_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_n_2757_, lean_object* v_p_2758_, lean_object* v_xs_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Vector_countP(v_00_u03b1_2756_, v_n_2757_, v_p_2758_, v_xs_2759_);
lean_dec(v_n_2757_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2761_, lean_object* v_a_2762_, lean_object* v_x1_2763_, lean_object* v_x2_2764_){
_start:
{
lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2765_ = lean_apply_2(v_inst_2761_, v_x1_2763_, v_a_2762_);
v___x_2766_ = lean_unbox(v___x_2765_);
if (v___x_2766_ == 0)
{
lean_inc(v_x2_2764_);
return v_x2_2764_;
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = lean_nat_add(v_x2_2764_, v___x_2767_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2769_, lean_object* v_a_2770_, lean_object* v_x1_2771_, lean_object* v_x2_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Vector_count___redArg___lam__0(v_inst_2769_, v_a_2770_, v_x1_2771_, v_x2_2772_);
lean_dec(v_x2_2772_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2774_, lean_object* v_a_2775_, lean_object* v_xs_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = lean_array_get_size(v_xs_2776_);
v___x_2779_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2780_ = lean_nat_dec_lt(v___x_2777_, v___x_2778_);
if (v___x_2780_ == 0)
{
lean_dec_ref(v_xs_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_inst_2774_);
return v___x_2777_;
}
else
{
lean_object* v___f_2781_; size_t v___x_2782_; size_t v___x_2783_; lean_object* v___x_2784_; 
v___f_2781_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2781_, 0, v_inst_2774_);
lean_closure_set(v___f_2781_, 1, v_a_2775_);
v___x_2782_ = lean_usize_of_nat(v___x_2778_);
v___x_2783_ = ((size_t)0ULL);
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2779_, v___f_2781_, v_xs_2776_, v___x_2782_, v___x_2783_, v___x_2777_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2785_, lean_object* v_n_2786_, lean_object* v_inst_2787_, lean_object* v_a_2788_, lean_object* v_xs_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2790_ = lean_unsigned_to_nat(0u);
v___x_2791_ = lean_array_get_size(v_xs_2789_);
v___x_2792_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2793_ = lean_nat_dec_lt(v___x_2790_, v___x_2791_);
if (v___x_2793_ == 0)
{
lean_dec_ref(v_xs_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_inst_2787_);
return v___x_2790_;
}
else
{
lean_object* v___f_2794_; size_t v___x_2795_; size_t v___x_2796_; lean_object* v___x_2797_; 
v___f_2794_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2794_, 0, v_inst_2787_);
lean_closure_set(v___f_2794_, 1, v_a_2788_);
v___x_2795_ = lean_usize_of_nat(v___x_2791_);
v___x_2796_ = ((size_t)0ULL);
v___x_2797_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2792_, v___f_2794_, v_xs_2789_, v___x_2795_, v___x_2796_, v___x_2790_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_n_2799_, lean_object* v_inst_2800_, lean_object* v_a_2801_, lean_object* v_xs_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Vector_count(v_00_u03b1_2798_, v_n_2799_, v_inst_2800_, v_a_2801_, v_xs_2802_);
lean_dec(v_n_2799_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2804_, lean_object* v_xs_2805_, lean_object* v_a_2806_, lean_object* v_b_2807_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Array_replace___redArg(v_inst_2804_, v_xs_2805_, v_a_2806_, v_b_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2809_, lean_object* v_n_2810_, lean_object* v_inst_2811_, lean_object* v_xs_2812_, lean_object* v_a_2813_, lean_object* v_b_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Array_replace___redArg(v_inst_2811_, v_xs_2812_, v_a_2813_, v_b_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2816_, lean_object* v_n_2817_, lean_object* v_inst_2818_, lean_object* v_xs_2819_, lean_object* v_a_2820_, lean_object* v_b_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Vector_replace(v_00_u03b1_2816_, v_n_2817_, v_inst_2818_, v_xs_2819_, v_a_2820_, v_b_2821_);
lean_dec(v_n_2817_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2823_, lean_object* v_x1_2824_, lean_object* v_x2_2825_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_apply_2(v_inst_2823_, v_x1_2824_, v_x2_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_xs_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2830_ = lean_array_get_size(v_xs_2829_);
v___x_2831_ = lean_unsigned_to_nat(0u);
v___x_2832_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2833_ = lean_nat_dec_lt(v___x_2831_, v___x_2830_);
if (v___x_2833_ == 0)
{
lean_dec_ref(v_xs_2829_);
lean_dec(v_inst_2827_);
return v_inst_2828_;
}
else
{
lean_object* v___f_2834_; size_t v___x_2835_; size_t v___x_2836_; lean_object* v___x_2837_; 
v___f_2834_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2834_, 0, v_inst_2827_);
v___x_2835_ = lean_usize_of_nat(v___x_2830_);
v___x_2836_ = ((size_t)0ULL);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2832_, v___f_2834_, v_xs_2829_, v___x_2835_, v___x_2836_, v_inst_2828_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2838_, lean_object* v_n_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_xs_2842_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2843_ = lean_array_get_size(v_xs_2842_);
v___x_2844_ = lean_unsigned_to_nat(0u);
v___x_2845_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2846_ = lean_nat_dec_lt(v___x_2844_, v___x_2843_);
if (v___x_2846_ == 0)
{
lean_dec_ref(v_xs_2842_);
lean_dec(v_inst_2840_);
return v_inst_2841_;
}
else
{
lean_object* v___f_2847_; size_t v___x_2848_; size_t v___x_2849_; lean_object* v___x_2850_; 
v___f_2847_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2847_, 0, v_inst_2840_);
v___x_2848_ = lean_usize_of_nat(v___x_2843_);
v___x_2849_ = ((size_t)0ULL);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2845_, v___f_2847_, v_xs_2842_, v___x_2848_, v___x_2849_, v_inst_2841_);
return v___x_2850_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_n_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_xs_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Vector_sum(v_00_u03b1_2851_, v_n_2852_, v_inst_2853_, v_inst_2854_, v_xs_2855_);
lean_dec(v_n_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_xs_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2860_ = lean_array_get_size(v_xs_2859_);
v___x_2861_ = lean_unsigned_to_nat(0u);
v___x_2862_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2863_ = lean_nat_dec_lt(v___x_2861_, v___x_2860_);
if (v___x_2863_ == 0)
{
lean_dec_ref(v_xs_2859_);
lean_dec(v_inst_2857_);
return v_inst_2858_;
}
else
{
lean_object* v___f_2864_; size_t v___x_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
v___f_2864_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2864_, 0, v_inst_2857_);
v___x_2865_ = lean_usize_of_nat(v___x_2860_);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2862_, v___f_2864_, v_xs_2859_, v___x_2865_, v___x_2866_, v_inst_2858_);
return v___x_2867_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2868_, lean_object* v_n_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_xs_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2873_ = lean_array_get_size(v_xs_2872_);
v___x_2874_ = lean_unsigned_to_nat(0u);
v___x_2875_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2876_ = lean_nat_dec_lt(v___x_2874_, v___x_2873_);
if (v___x_2876_ == 0)
{
lean_dec_ref(v_xs_2872_);
lean_dec(v_inst_2870_);
return v_inst_2871_;
}
else
{
lean_object* v___f_2877_; size_t v___x_2878_; size_t v___x_2879_; lean_object* v___x_2880_; 
v___f_2877_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2877_, 0, v_inst_2870_);
v___x_2878_ = lean_usize_of_nat(v___x_2873_);
v___x_2879_ = ((size_t)0ULL);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2875_, v___f_2877_, v_xs_2872_, v___x_2878_, v___x_2879_, v_inst_2871_);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2881_, lean_object* v_n_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_xs_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l_Vector_prod(v_00_u03b1_2881_, v_n_2882_, v_inst_2883_, v_inst_2884_, v_xs_2885_);
lean_dec(v_n_2882_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2887_, lean_object* v_n_2888_, lean_object* v_a_2889_, lean_object* v_xs_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_nat_sub(v_n_2888_, v_m_2887_);
v___x_2892_ = lean_mk_array(v___x_2891_, v_a_2889_);
v___x_2893_ = l_Array_append___redArg(v___x_2892_, v_xs_2890_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2894_, lean_object* v_n_2895_, lean_object* v_a_2896_, lean_object* v_xs_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Vector_leftpad___redArg(v_m_2894_, v_n_2895_, v_a_2896_, v_xs_2897_);
lean_dec_ref(v_xs_2897_);
lean_dec(v_n_2895_);
lean_dec(v_m_2894_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2899_, lean_object* v_m_2900_, lean_object* v_n_2901_, lean_object* v_a_2902_, lean_object* v_xs_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_nat_sub(v_n_2901_, v_m_2900_);
v___x_2905_ = lean_mk_array(v___x_2904_, v_a_2902_);
v___x_2906_ = l_Array_append___redArg(v___x_2905_, v_xs_2903_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2907_, lean_object* v_m_2908_, lean_object* v_n_2909_, lean_object* v_a_2910_, lean_object* v_xs_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Vector_leftpad(v_00_u03b1_2907_, v_m_2908_, v_n_2909_, v_a_2910_, v_xs_2911_);
lean_dec_ref(v_xs_2911_);
lean_dec(v_n_2909_);
lean_dec(v_m_2908_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2913_, lean_object* v_n_2914_, lean_object* v_a_2915_, lean_object* v_xs_2916_){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2917_ = lean_nat_sub(v_n_2914_, v_m_2913_);
v___x_2918_ = lean_mk_array(v___x_2917_, v_a_2915_);
v___x_2919_ = l_Array_append___redArg(v_xs_2916_, v___x_2918_);
lean_dec_ref(v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2920_, lean_object* v_n_2921_, lean_object* v_a_2922_, lean_object* v_xs_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Vector_rightpad___redArg(v_m_2920_, v_n_2921_, v_a_2922_, v_xs_2923_);
lean_dec(v_n_2921_);
lean_dec(v_m_2920_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2925_, lean_object* v_m_2926_, lean_object* v_n_2927_, lean_object* v_a_2928_, lean_object* v_xs_2929_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_nat_sub(v_n_2927_, v_m_2926_);
v___x_2931_ = lean_mk_array(v___x_2930_, v_a_2928_);
v___x_2932_ = l_Array_append___redArg(v_xs_2929_, v___x_2931_);
lean_dec_ref(v___x_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2933_, lean_object* v_m_2934_, lean_object* v_n_2935_, lean_object* v_a_2936_, lean_object* v_xs_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Vector_rightpad(v_00_u03b1_2933_, v_m_2934_, v_n_2935_, v_a_2936_, v_xs_2937_);
lean_dec(v_n_2935_);
lean_dec(v_m_2934_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2939_, lean_object* v_a_2940_, lean_object* v_h_2941_, lean_object* v_b_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = lean_apply_3(v_f_2939_, v_a_2940_, lean_box(0), v_b_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2944_, lean_object* v_00_u03b2_2945_, lean_object* v_xs_2946_, lean_object* v_b_2947_, lean_object* v_f_2948_){
_start:
{
lean_object* v___f_2949_; size_t v_sz_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___f_2949_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2949_, 0, v_f_2948_);
v_sz_2950_ = lean_array_size(v_xs_2946_);
v___x_2951_ = ((size_t)0ULL);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2944_, v_xs_2946_, v___f_2949_, v_sz_2950_, v___x_2951_, v_b_2947_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2953_){
_start:
{
lean_object* v___f_2954_; 
v___f_2954_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2954_, 0, v_inst_2953_);
return v___f_2954_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2955_, lean_object* v_00_u03b1_2956_, lean_object* v_n_2957_, lean_object* v_inst_2958_){
_start:
{
lean_object* v___f_2959_; 
v___f_2959_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2959_, 0, v_inst_2958_);
return v___f_2959_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2960_, lean_object* v_00_u03b1_2961_, lean_object* v_n_2962_, lean_object* v_inst_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2960_, v_00_u03b1_2961_, v_n_2962_, v_inst_2963_);
lean_dec(v_n_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2965_, lean_object* v_inst_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2967_, 0, lean_box(0));
lean_closure_set(v___x_2967_, 1, lean_box(0));
lean_closure_set(v___x_2967_, 2, v_n_2965_);
lean_closure_set(v___x_2967_, 3, v_inst_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2968_, lean_object* v_00_u03b1_2969_, lean_object* v_n_2970_, lean_object* v_inst_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2972_, 0, lean_box(0));
lean_closure_set(v___x_2972_, 1, lean_box(0));
lean_closure_set(v___x_2972_, 2, v_n_2970_);
lean_closure_set(v___x_2972_, 3, v_inst_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2973_, lean_object* v_n_2974_, lean_object* v_inst_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_box(0);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_n_2978_, lean_object* v_inst_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Vector_instLT(v_00_u03b1_2977_, v_n_2978_, v_inst_2979_);
lean_dec(v_n_2978_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2981_, lean_object* v_n_2982_, lean_object* v_inst_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = lean_box(0);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2985_, lean_object* v_n_2986_, lean_object* v_inst_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Vector_instLE(v_00_u03b1_2985_, v_n_2986_, v_inst_2987_);
lean_dec(v_n_2986_);
return v_res_2988_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2996_ = l_Lean_mkAtom(v___x_2995_);
return v___x_2996_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2998_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2999_ = lean_array_push(v___x_2998_, v___x_2997_);
return v___x_2999_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_3013_ = l_Lean_mkAtom(v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_3015_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3016_ = lean_array_push(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3022_ = lean_string_utf8_byte_size(v___x_3021_);
return v___x_3022_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_3026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
lean_ctor_set(v___x_3026_, 2, v___x_3023_);
return v___x_3026_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_3030_ = lean_box(2);
v___x_3031_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v___x_3029_);
lean_ctor_set(v___x_3031_, 2, v___x_3028_);
lean_ctor_set(v___x_3031_, 3, v___x_3027_);
return v___x_3031_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3033_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3034_ = lean_array_push(v___x_3033_, v___x_3032_);
return v___x_3034_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3035_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3036_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3037_ = lean_box(2);
v___x_3038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v___x_3036_);
lean_ctor_set(v___x_3038_, 2, v___x_3035_);
return v___x_3038_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3040_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3039_);
return v___x_3041_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3042_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3043_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3044_ = lean_box(2);
v___x_3045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v___x_3043_);
lean_ctor_set(v___x_3045_, 2, v___x_3042_);
return v___x_3045_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3047_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3048_ = lean_array_push(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3060_ = l_Lean_mkAtom(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3062_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3063_ = lean_array_push(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3065_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3066_ = lean_array_push(v___x_3065_, v___x_3064_);
return v___x_3066_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3067_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3068_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3069_ = lean_box(2);
v___x_3070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3069_);
lean_ctor_set(v___x_3070_, 1, v___x_3068_);
lean_ctor_set(v___x_3070_, 2, v___x_3067_);
return v___x_3070_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3072_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3073_ = lean_array_push(v___x_3072_, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3076_ = l_Lean_mkAtom(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3078_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3079_ = lean_array_push(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3081_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3082_ = lean_array_push(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3083_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3084_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3085_ = lean_box(2);
v___x_3086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___x_3084_);
lean_ctor_set(v___x_3086_, 2, v___x_3083_);
return v___x_3086_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3087_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3088_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3089_ = lean_array_push(v___x_3088_, v___x_3087_);
return v___x_3089_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3091_ = l_Lean_mkAtom(v___x_3090_);
return v___x_3091_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3094_ = lean_array_push(v___x_3093_, v___x_3092_);
return v___x_3094_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3095_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3096_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3097_ = lean_box(2);
v___x_3098_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
lean_ctor_set(v___x_3098_, 1, v___x_3096_);
lean_ctor_set(v___x_3098_, 2, v___x_3095_);
return v___x_3098_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3100_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3101_ = lean_array_push(v___x_3100_, v___x_3099_);
return v___x_3101_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3102_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3103_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3104_ = lean_box(2);
v___x_3105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___x_3103_);
lean_ctor_set(v___x_3105_, 2, v___x_3102_);
return v___x_3105_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3106_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3107_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3108_ = lean_array_push(v___x_3107_, v___x_3106_);
return v___x_3108_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3109_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3110_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3111_ = lean_box(2);
v___x_3112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
lean_ctor_set(v___x_3112_, 1, v___x_3110_);
lean_ctor_set(v___x_3112_, 2, v___x_3109_);
return v___x_3112_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3113_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3114_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3115_ = lean_array_push(v___x_3114_, v___x_3113_);
return v___x_3115_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3116_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3117_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3118_ = lean_box(2);
v___x_3119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
lean_ctor_set(v___x_3119_, 1, v___x_3117_);
lean_ctor_set(v___x_3119_, 2, v___x_3116_);
return v___x_3119_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3121_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3122_ = lean_array_push(v___x_3121_, v___x_3120_);
return v___x_3122_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3123_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3124_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3125_ = lean_box(2);
v___x_3126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___x_3124_);
lean_ctor_set(v___x_3126_, 2, v___x_3123_);
return v___x_3126_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3128_, lean_object* v_xs_3129_, lean_object* v_ys_3130_, lean_object* v_lt_3131_, lean_object* v_inst_3132_, lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v_next_3135_, lean_object* v_acc_3136_, lean_object* v_h_3137_, lean_object* v_G_3138_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_nat_dec_lt(v_next_3135_, v_n_3128_);
if (v___x_3139_ == 0)
{
lean_dec_ref(v_G_3138_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v_inst_3132_);
lean_dec_ref(v_lt_3131_);
lean_inc_ref(v_acc_3136_);
return v_acc_3136_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3140_ = lean_array_fget_borrowed(v_xs_3129_, v_next_3135_);
v___x_3141_ = lean_array_fget_borrowed(v_ys_3130_, v_next_3135_);
lean_inc(v___x_3141_);
lean_inc(v___x_3140_);
v___x_3142_ = lean_apply_2(v_lt_3131_, v___x_3140_, v___x_3141_);
v___x_3143_ = lean_unbox(v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
lean_inc(v___x_3141_);
lean_inc(v___x_3140_);
v___x_3144_ = lean_apply_2(v_inst_3132_, v___x_3140_, v___x_3141_);
v___x_3145_ = lean_unbox(v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec_ref(v_G_3138_);
lean_dec_ref(v___x_3134_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3142_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v___x_3133_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_add(v_next_3135_, v___x_3148_);
v___x_3150_ = lean_apply_4(v_G_3138_, v___x_3149_, v___x_3134_, lean_box(0), lean_box(0));
return v___x_3150_;
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref(v_G_3138_);
lean_dec_ref(v___x_3134_);
lean_dec_ref(v_inst_3132_);
v___x_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3142_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v___x_3133_);
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3153_, lean_object* v_xs_3154_, lean_object* v_ys_3155_, lean_object* v_lt_3156_, lean_object* v_inst_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_next_3160_, lean_object* v_acc_3161_, lean_object* v_h_3162_, lean_object* v_G_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Vector_lex___redArg___lam__0(v_n_3153_, v_xs_3154_, v_ys_3155_, v_lt_3156_, v_inst_3157_, v___x_3158_, v___x_3159_, v_next_3160_, v_acc_3161_, v_h_3162_, v_G_3163_);
lean_dec_ref(v_acc_3161_);
lean_dec(v_next_3160_);
lean_dec_ref(v_ys_3155_);
lean_dec_ref(v_xs_3154_);
lean_dec(v_n_3153_);
return v_res_3164_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3168_, lean_object* v_inst_3169_, lean_object* v_xs_3170_, lean_object* v_ys_3171_, lean_object* v_lt_3172_){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; lean_object* v_fst_3178_; 
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = lean_box(0);
v___x_3175_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3176_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3176_, 0, v_n_3168_);
lean_closure_set(v___f_3176_, 1, v_xs_3170_);
lean_closure_set(v___f_3176_, 2, v_ys_3171_);
lean_closure_set(v___f_3176_, 3, v_lt_3172_);
lean_closure_set(v___f_3176_, 4, v_inst_3169_);
lean_closure_set(v___f_3176_, 5, v___x_3174_);
lean_closure_set(v___f_3176_, 6, v___x_3175_);
v___x_3177_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3176_, v___x_3173_, v___x_3175_, lean_box(0));
v_fst_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_fst_3178_);
lean_dec(v___x_3177_);
if (lean_obj_tag(v_fst_3178_) == 0)
{
uint8_t v___x_3179_; 
v___x_3179_ = 0;
return v___x_3179_;
}
else
{
lean_object* v_val_3180_; uint8_t v___x_3181_; 
v_val_3180_ = lean_ctor_get(v_fst_3178_, 0);
lean_inc(v_val_3180_);
lean_dec_ref(v_fst_3178_);
v___x_3181_ = lean_unbox(v_val_3180_);
lean_dec(v_val_3180_);
return v___x_3181_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3182_, lean_object* v_inst_3183_, lean_object* v_xs_3184_, lean_object* v_ys_3185_, lean_object* v_lt_3186_){
_start:
{
uint8_t v_res_3187_; lean_object* v_r_3188_; 
v_res_3187_ = l_Vector_lex___redArg(v_n_3182_, v_inst_3183_, v_xs_3184_, v_ys_3185_, v_lt_3186_);
v_r_3188_ = lean_box(v_res_3187_);
return v_r_3188_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3189_, lean_object* v_n_3190_, lean_object* v_inst_3191_, lean_object* v_xs_3192_, lean_object* v_ys_3193_, lean_object* v_lt_3194_){
_start:
{
uint8_t v___x_3195_; 
v___x_3195_ = l_Vector_lex___redArg(v_n_3190_, v_inst_3191_, v_xs_3192_, v_ys_3193_, v_lt_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3196_, lean_object* v_n_3197_, lean_object* v_inst_3198_, lean_object* v_xs_3199_, lean_object* v_ys_3200_, lean_object* v_lt_3201_){
_start:
{
uint8_t v_res_3202_; lean_object* v_r_3203_; 
v_res_3202_ = l_Vector_lex(v_00_u03b1_3196_, v_n_3197_, v_inst_3198_, v_xs_3199_, v_ys_3200_, v_lt_3201_);
v_r_3203_ = lean_box(v_res_3202_);
return v_r_3203_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
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
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Array_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MapIdx(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
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
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
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
