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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
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
lean_object* v_toApplicative_749_; lean_object* v_toPure_750_; lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v_toApplicative_749_ = lean_ctor_get(v_inst_745_, 0);
v_toPure_750_ = lean_ctor_get(v_toApplicative_749_, 1);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_array_get_size(v_xs_748_);
v___x_753_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_inc(v_toPure_750_);
lean_dec_ref(v_xs_748_);
lean_dec(v_f_746_);
lean_dec_ref(v_inst_745_);
v___x_754_ = lean_apply_2(v_toPure_750_, lean_box(0), v_b_747_);
return v___x_754_;
}
else
{
uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_le(v___x_752_, v___x_752_);
if (v___x_755_ == 0)
{
if (v___x_753_ == 0)
{
lean_object* v___x_756_; 
lean_inc(v_toPure_750_);
lean_dec_ref(v_xs_748_);
lean_dec(v_f_746_);
lean_dec_ref(v_inst_745_);
v___x_756_ = lean_apply_2(v_toPure_750_, lean_box(0), v_b_747_);
return v___x_756_;
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_752_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v_f_746_, v_xs_748_, v___x_757_, v___x_758_, v_b_747_);
return v___x_759_;
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_752_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_745_, v_f_746_, v_xs_748_, v___x_760_, v___x_761_, v_b_747_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM(lean_object* v_m_763_, lean_object* v_00_u03b2_764_, lean_object* v_00_u03b1_765_, lean_object* v_n_766_, lean_object* v_inst_767_, lean_object* v_f_768_, lean_object* v_b_769_, lean_object* v_xs_770_){
_start:
{
lean_object* v_toApplicative_771_; lean_object* v_toPure_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_toApplicative_771_ = lean_ctor_get(v_inst_767_, 0);
v_toPure_772_ = lean_ctor_get(v_toApplicative_771_, 1);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_array_get_size(v_xs_770_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_inc(v_toPure_772_);
lean_dec_ref(v_xs_770_);
lean_dec(v_f_768_);
lean_dec_ref(v_inst_767_);
v___x_776_ = lean_apply_2(v_toPure_772_, lean_box(0), v_b_769_);
return v___x_776_;
}
else
{
uint8_t v___x_777_; 
v___x_777_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_777_ == 0)
{
if (v___x_775_ == 0)
{
lean_object* v___x_778_; 
lean_inc(v_toPure_772_);
lean_dec_ref(v_xs_770_);
lean_dec(v_f_768_);
lean_dec_ref(v_inst_767_);
v___x_778_ = lean_apply_2(v_toPure_772_, lean_box(0), v_b_769_);
return v___x_778_;
}
else
{
size_t v___x_779_; size_t v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((size_t)0ULL);
v___x_780_ = lean_usize_of_nat(v___x_774_);
v___x_781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_767_, v_f_768_, v_xs_770_, v___x_779_, v___x_780_, v_b_769_);
return v___x_781_;
}
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_774_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_767_, v_f_768_, v_xs_770_, v___x_782_, v___x_783_, v_b_769_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldlM___boxed(lean_object* v_m_785_, lean_object* v_00_u03b2_786_, lean_object* v_00_u03b1_787_, lean_object* v_n_788_, lean_object* v_inst_789_, lean_object* v_f_790_, lean_object* v_b_791_, lean_object* v_xs_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Vector_foldlM(v_m_785_, v_00_u03b2_786_, v_00_u03b1_787_, v_n_788_, v_inst_789_, v_f_790_, v_b_791_, v_xs_792_);
lean_dec(v_n_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___redArg(lean_object* v_inst_794_, lean_object* v_f_795_, lean_object* v_b_796_, lean_object* v_xs_797_){
_start:
{
lean_object* v_toApplicative_798_; lean_object* v_toPure_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_toApplicative_798_ = lean_ctor_get(v_inst_794_, 0);
v_toPure_799_ = lean_ctor_get(v_toApplicative_798_, 1);
v___x_800_ = lean_array_get_size(v_xs_797_);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_nat_dec_lt(v___x_801_, v___x_800_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_inc(v_toPure_799_);
lean_dec_ref(v_xs_797_);
lean_dec(v_f_795_);
lean_dec_ref(v_inst_794_);
v___x_803_ = lean_apply_2(v_toPure_799_, lean_box(0), v_b_796_);
return v___x_803_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_usize_of_nat(v___x_800_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_794_, v_f_795_, v_xs_797_, v___x_804_, v___x_805_, v_b_796_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM(lean_object* v_m_807_, lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_n_810_, lean_object* v_inst_811_, lean_object* v_f_812_, lean_object* v_b_813_, lean_object* v_xs_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_toPure_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_811_, 0);
v_toPure_816_ = lean_ctor_get(v_toApplicative_815_, 1);
v___x_817_ = lean_array_get_size(v_xs_814_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_nat_dec_lt(v___x_818_, v___x_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_inc(v_toPure_816_);
lean_dec_ref(v_xs_814_);
lean_dec(v_f_812_);
lean_dec_ref(v_inst_811_);
v___x_820_ = lean_apply_2(v_toPure_816_, lean_box(0), v_b_813_);
return v___x_820_;
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_usize_of_nat(v___x_817_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_811_, v_f_812_, v_xs_814_, v___x_821_, v___x_822_, v_b_813_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldrM___boxed(lean_object* v_m_824_, lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_n_827_, lean_object* v_inst_828_, lean_object* v_f_829_, lean_object* v_b_830_, lean_object* v_xs_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Vector_foldrM(v_m_824_, v_00_u03b1_825_, v_00_u03b2_826_, v_n_827_, v_inst_828_, v_f_829_, v_b_830_, v_xs_831_);
lean_dec(v_n_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg___lam__0(lean_object* v_f_833_, lean_object* v_x1_834_, lean_object* v_x2_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_f_833_, v_x1_834_, v_x2_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___redArg(lean_object* v_f_856_, lean_object* v_b_857_, lean_object* v_xs_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_xs_858_);
v___x_861_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_862_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_862_ == 0)
{
lean_dec_ref(v_xs_858_);
lean_dec(v_f_856_);
return v_b_857_;
}
else
{
lean_object* v___f_863_; uint8_t v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_863_, 0, v_f_856_);
v___x_864_ = lean_nat_dec_le(v___x_860_, v___x_860_);
if (v___x_864_ == 0)
{
if (v___x_862_ == 0)
{
lean_dec_ref(v___f_863_);
lean_dec_ref(v_xs_858_);
return v_b_857_;
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_860_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_861_, v___f_863_, v_xs_858_, v___x_865_, v___x_866_, v_b_857_);
return v___x_867_;
}
}
else
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((size_t)0ULL);
v___x_869_ = lean_usize_of_nat(v___x_860_);
v___x_870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_861_, v___f_863_, v_xs_858_, v___x_868_, v___x_869_, v_b_857_);
return v___x_870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl(lean_object* v_00_u03b2_871_, lean_object* v_00_u03b1_872_, lean_object* v_n_873_, lean_object* v_f_874_, lean_object* v_b_875_, lean_object* v_xs_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_xs_876_);
v___x_879_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_880_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_xs_876_);
lean_dec(v_f_874_);
return v_b_875_;
}
else
{
lean_object* v___f_881_; uint8_t v___x_882_; 
v___f_881_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_881_, 0, v_f_874_);
v___x_882_ = lean_nat_dec_le(v___x_878_, v___x_878_);
if (v___x_882_ == 0)
{
if (v___x_880_ == 0)
{
lean_dec_ref(v___f_881_);
lean_dec_ref(v_xs_876_);
return v_b_875_;
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_878_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_xs_876_, v___x_883_, v___x_884_, v_b_875_);
return v___x_885_;
}
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((size_t)0ULL);
v___x_887_ = lean_usize_of_nat(v___x_878_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_881_, v_xs_876_, v___x_886_, v___x_887_, v_b_875_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldl___boxed(lean_object* v_00_u03b2_889_, lean_object* v_00_u03b1_890_, lean_object* v_n_891_, lean_object* v_f_892_, lean_object* v_b_893_, lean_object* v_xs_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Vector_foldl(v_00_u03b2_889_, v_00_u03b1_890_, v_n_891_, v_f_892_, v_b_893_, v_xs_894_);
lean_dec(v_n_891_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___redArg(lean_object* v_f_896_, lean_object* v_b_897_, lean_object* v_xs_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_899_ = lean_array_get_size(v_xs_898_);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_899_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_xs_898_);
lean_dec(v_f_896_);
return v_b_897_;
}
else
{
lean_object* v___f_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___f_903_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_903_, 0, v_f_896_);
v___x_904_ = lean_usize_of_nat(v___x_899_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_901_, v___f_903_, v_xs_898_, v___x_904_, v___x_905_, v_b_897_);
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_n_909_, lean_object* v_f_910_, lean_object* v_b_911_, lean_object* v_xs_912_){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_913_ = lean_array_get_size(v_xs_912_);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_913_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_xs_912_);
lean_dec(v_f_910_);
return v_b_911_;
}
else
{
lean_object* v___f_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___f_917_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_917_, 0, v_f_910_);
v___x_918_ = lean_usize_of_nat(v___x_913_);
v___x_919_ = ((size_t)0ULL);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_915_, v___f_917_, v_xs_912_, v___x_918_, v___x_919_, v_b_911_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_foldr___boxed(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_n_923_, lean_object* v_f_924_, lean_object* v_b_925_, lean_object* v_xs_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Vector_foldr(v_00_u03b1_921_, v_00_u03b2_922_, v_n_923_, v_f_924_, v_b_925_, v_xs_926_);
lean_dec(v_n_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg(lean_object* v_xs_928_, lean_object* v_ys_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Array_append___redArg(v_xs_928_, v_ys_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___redArg___boxed(lean_object* v_xs_931_, lean_object* v_ys_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Vector_append___redArg(v_xs_931_, v_ys_932_);
lean_dec_ref(v_ys_932_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Vector_append(lean_object* v_00_u03b1_934_, lean_object* v_n_935_, lean_object* v_m_936_, lean_object* v_xs_937_, lean_object* v_ys_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Array_append___redArg(v_xs_937_, v_ys_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Vector_append___boxed(lean_object* v_00_u03b1_940_, lean_object* v_n_941_, lean_object* v_m_942_, lean_object* v_xs_943_, lean_object* v_ys_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Vector_append(v_00_u03b1_940_, v_n_941_, v_m_942_, v_xs_943_, v_ys_944_);
lean_dec_ref(v_ys_944_);
lean_dec(v_m_942_);
lean_dec(v_n_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat___redArg(lean_object* v_n_946_, lean_object* v_m_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_closure((void*)(l_Vector_append___boxed), 5, 3);
lean_closure_set(v___x_948_, 0, lean_box(0));
lean_closure_set(v___x_948_, 1, v_n_946_);
lean_closure_set(v___x_948_, 2, v_m_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Vector_instHAppendHAddNat(lean_object* v_00_u03b1_949_, lean_object* v_n_950_, lean_object* v_m_951_){
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
LEAN_EXPORT lean_object* l_Vector_cast___redArg(lean_object* v_xs_953_){
_start:
{
lean_inc_ref(v_xs_953_);
return v_xs_953_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___redArg___boxed(lean_object* v_xs_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Vector_cast___redArg(v_xs_954_);
lean_dec_ref(v_xs_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast(lean_object* v_n_956_, lean_object* v_m_957_, lean_object* v_00_u03b1_958_, lean_object* v_h_959_, lean_object* v_xs_960_){
_start:
{
lean_inc_ref(v_xs_960_);
return v_xs_960_;
}
}
LEAN_EXPORT lean_object* l_Vector_cast___boxed(lean_object* v_n_961_, lean_object* v_m_962_, lean_object* v_00_u03b1_963_, lean_object* v_h_964_, lean_object* v_xs_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Vector_cast(v_n_961_, v_m_962_, v_00_u03b1_963_, v_h_964_, v_xs_965_);
lean_dec_ref(v_xs_965_);
lean_dec(v_m_962_);
lean_dec(v_n_961_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg(lean_object* v_xs_967_, lean_object* v_start_968_, lean_object* v_stop_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Array_extract___redArg(v_xs_967_, v_start_968_, v_stop_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___redArg___boxed(lean_object* v_xs_971_, lean_object* v_start_972_, lean_object* v_stop_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Vector_extract___redArg(v_xs_971_, v_start_972_, v_stop_973_);
lean_dec_ref(v_xs_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract(lean_object* v_00_u03b1_975_, lean_object* v_n_976_, lean_object* v_xs_977_, lean_object* v_start_978_, lean_object* v_stop_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Array_extract___redArg(v_xs_977_, v_start_978_, v_stop_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Vector_extract___boxed(lean_object* v_00_u03b1_981_, lean_object* v_n_982_, lean_object* v_xs_983_, lean_object* v_start_984_, lean_object* v_stop_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Vector_extract(v_00_u03b1_981_, v_n_982_, v_xs_983_, v_start_984_, v_stop_985_);
lean_dec_ref(v_xs_983_);
lean_dec(v_n_982_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg(lean_object* v_n_987_, lean_object* v_xs_988_, lean_object* v_i_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = l_Array_extract___redArg(v_xs_988_, v___x_990_, v_i_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___redArg___boxed(lean_object* v_n_992_, lean_object* v_xs_993_, lean_object* v_i_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Vector_take___redArg(v_n_992_, v_xs_993_, v_i_994_);
lean_dec_ref(v_xs_993_);
lean_dec(v_n_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Vector_take(lean_object* v_00_u03b1_996_, lean_object* v_n_997_, lean_object* v_xs_998_, lean_object* v_i_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = l_Array_extract___redArg(v_xs_998_, v___x_1000_, v_i_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Vector_take___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_n_1003_, lean_object* v_xs_1004_, lean_object* v_i_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Vector_take(v_00_u03b1_1002_, v_n_1003_, v_xs_1004_, v_i_1005_);
lean_dec_ref(v_xs_1004_);
lean_dec(v_n_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg(lean_object* v_xs_1007_, lean_object* v_i_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_array_get_size(v_xs_1007_);
v___x_1010_ = l_Array_extract___redArg(v_xs_1007_, v_i_1008_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___redArg___boxed(lean_object* v_xs_1011_, lean_object* v_i_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Vector_drop___redArg(v_xs_1011_, v_i_1012_);
lean_dec_ref(v_xs_1011_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop(lean_object* v_00_u03b1_1014_, lean_object* v_n_1015_, lean_object* v_xs_1016_, lean_object* v_i_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_xs_1016_);
v___x_1019_ = l_Array_extract___redArg(v_xs_1016_, v_i_1017_, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Vector_drop___boxed(lean_object* v_00_u03b1_1020_, lean_object* v_n_1021_, lean_object* v_xs_1022_, lean_object* v_i_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Vector_drop(v_00_u03b1_1020_, v_n_1021_, v_xs_1022_, v_i_1023_);
lean_dec_ref(v_xs_1022_);
lean_dec(v_n_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg(lean_object* v_xs_1025_, lean_object* v_i_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Array_shrink___redArg(v_xs_1025_, v_i_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___redArg___boxed(lean_object* v_xs_1028_, lean_object* v_i_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Vector_shrink___redArg(v_xs_1028_, v_i_1029_);
lean_dec(v_i_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink(lean_object* v_00_u03b1_1031_, lean_object* v_n_1032_, lean_object* v_xs_1033_, lean_object* v_i_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Array_shrink___redArg(v_xs_1033_, v_i_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Vector_shrink___boxed(lean_object* v_00_u03b1_1036_, lean_object* v_n_1037_, lean_object* v_xs_1038_, lean_object* v_i_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Vector_shrink(v_00_u03b1_1036_, v_n_1037_, v_xs_1038_, v_i_1039_);
lean_dec(v_i_1039_);
lean_dec(v_n_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg___lam__0(lean_object* v_f_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_apply_1(v_f_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___redArg(lean_object* v_f_1044_, lean_object* v_xs_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_f_1044_);
v___x_1047_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1048_ = lean_array_size(v_xs_1045_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1047_, v___f_1046_, v_sz_1048_, v___x_1049_, v_xs_1045_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Vector_map(lean_object* v_00_u03b1_1051_, lean_object* v_00_u03b2_1052_, lean_object* v_n_1053_, lean_object* v_f_1054_, lean_object* v_xs_1055_){
_start:
{
lean_object* v___f_1056_; lean_object* v___x_1057_; size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
v___f_1056_ = lean_alloc_closure((void*)(l_Vector_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1056_, 0, v_f_1054_);
v___x_1057_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1058_ = lean_array_size(v_xs_1055_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1057_, v___f_1056_, v_sz_1058_, v___x_1059_, v_xs_1055_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Vector_map___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_n_1063_, lean_object* v_f_1064_, lean_object* v_xs_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Vector_map(v_00_u03b1_1061_, v_00_u03b2_1062_, v_n_1063_, v_f_1064_, v_xs_1065_);
lean_dec(v_n_1063_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg___lam__0(lean_object* v_f_1067_, lean_object* v_i_1068_, lean_object* v_a_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_apply_2(v_f_1067_, v_i_1068_, v_a_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___redArg(lean_object* v_f_1072_, lean_object* v_xs_1073_){
_start:
{
lean_object* v___f_1074_; lean_object* v___x_1075_; size_t v_sz_1076_; size_t v___x_1077_; lean_object* v___x_1078_; 
v___f_1074_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1074_, 0, v_f_1072_);
v___x_1075_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1076_ = lean_array_size(v_xs_1073_);
v___x_1077_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1073_);
v___x_1078_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1075_, v_xs_1073_, v___f_1074_, v_sz_1076_, v___x_1077_, v_xs_1073_);
lean_dec_ref(v_xs_1073_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_n_1081_, lean_object* v_f_1082_, lean_object* v_xs_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; size_t v_sz_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
v___f_1084_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1084_, 0, v_f_1082_);
v___x_1085_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1086_ = lean_array_size(v_xs_1083_);
v___x_1087_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1083_);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1085_, v_xs_1083_, v___f_1084_, v_sz_1086_, v___x_1087_, v_xs_1083_);
lean_dec_ref(v_xs_1083_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdx___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_n_1091_, lean_object* v_f_1092_, lean_object* v_xs_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Vector_mapIdx(v_00_u03b1_1089_, v_00_u03b2_1090_, v_n_1091_, v_f_1092_, v_xs_1093_);
lean_dec(v_n_1091_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg___lam__0(lean_object* v_f_1095_, lean_object* v_x1_1096_, lean_object* v_x2_1097_, lean_object* v_x3_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_apply_3(v_f_1095_, v_x1_1096_, v_x2_1097_, lean_box(0));
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___redArg(lean_object* v_xs_1100_, lean_object* v_f_1101_){
_start:
{
lean_object* v___f_1102_; lean_object* v___x_1103_; size_t v_sz_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1102_, 0, v_f_1101_);
v___x_1103_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1104_ = lean_array_size(v_xs_1100_);
v___x_1105_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1100_);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1103_, v_xs_1100_, v___f_1102_, v_sz_1104_, v___x_1105_, v_xs_1100_);
lean_dec_ref(v_xs_1100_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx(lean_object* v_00_u03b1_1107_, lean_object* v_n_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_xs_1110_, lean_object* v_f_1111_){
_start:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; 
v___f_1112_ = lean_alloc_closure((void*)(l_Vector_mapFinIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1112_, 0, v_f_1111_);
v___x_1113_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1114_ = lean_array_size(v_xs_1110_);
v___x_1115_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1110_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1113_, v_xs_1110_, v___f_1112_, v_sz_1114_, v___x_1115_, v_xs_1110_);
lean_dec_ref(v_xs_1110_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdx___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_n_1118_, lean_object* v_00_u03b2_1119_, lean_object* v_xs_1120_, lean_object* v_f_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Vector_mapFinIdx(v_00_u03b1_1117_, v_n_1118_, v_00_u03b2_1119_, v_xs_1120_, v_f_1121_);
lean_dec(v_n_1118_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed(lean_object* v_k_1123_, lean_object* v_acc_1124_, lean_object* v_n_1125_, lean_object* v_inst_1126_, lean_object* v_f_1127_, lean_object* v_xs_1128_, lean_object* v_____do__lift_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(v_k_1123_, v_acc_1124_, v_n_1125_, v_inst_1126_, v_f_1127_, v_xs_1128_, v_____do__lift_1129_);
lean_dec(v_k_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(lean_object* v_n_1131_, lean_object* v_inst_1132_, lean_object* v_f_1133_, lean_object* v_xs_1134_, lean_object* v_k_1135_, lean_object* v_acc_1136_){
_start:
{
lean_object* v_toApplicative_1137_; lean_object* v_toBind_1138_; lean_object* v_toPure_1139_; uint8_t v___x_1140_; 
v_toApplicative_1137_ = lean_ctor_get(v_inst_1132_, 0);
v_toBind_1138_ = lean_ctor_get(v_inst_1132_, 1);
lean_inc(v_toBind_1138_);
v_toPure_1139_ = lean_ctor_get(v_toApplicative_1137_, 1);
v___x_1140_ = lean_nat_dec_lt(v_k_1135_, v_n_1131_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_inc(v_toPure_1139_);
lean_dec(v_toBind_1138_);
lean_dec(v_k_1135_);
lean_dec_ref(v_xs_1134_);
lean_dec(v_f_1133_);
lean_dec_ref(v_inst_1132_);
lean_dec(v_n_1131_);
v___x_1141_ = lean_apply_2(v_toPure_1139_, lean_box(0), v_acc_1136_);
return v___x_1141_;
}
else
{
lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc_ref(v_xs_1134_);
lean_inc(v_f_1133_);
lean_inc(v_k_1135_);
v___f_1142_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1142_, 0, v_k_1135_);
lean_closure_set(v___f_1142_, 1, v_acc_1136_);
lean_closure_set(v___f_1142_, 2, v_n_1131_);
lean_closure_set(v___f_1142_, 3, v_inst_1132_);
lean_closure_set(v___f_1142_, 4, v_f_1133_);
lean_closure_set(v___f_1142_, 5, v_xs_1134_);
v___x_1143_ = lean_array_fget(v_xs_1134_, v_k_1135_);
lean_dec(v_k_1135_);
lean_dec_ref(v_xs_1134_);
v___x_1144_ = lean_apply_1(v_f_1133_, v___x_1143_);
v___x_1145_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v___x_1144_, v___f_1142_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg___lam__0(lean_object* v_k_1146_, lean_object* v_acc_1147_, lean_object* v_n_1148_, lean_object* v_inst_1149_, lean_object* v_f_1150_, lean_object* v_xs_1151_, lean_object* v_____do__lift_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_k_1146_, v___x_1153_);
v___x_1155_ = lean_array_push(v_acc_1147_, v_____do__lift_1152_);
v___x_1156_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1148_, v_inst_1149_, v_f_1150_, v_xs_1151_, v___x_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go(lean_object* v_m_1157_, lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_n_1160_, lean_object* v_inst_1161_, lean_object* v_f_1162_, lean_object* v_xs_1163_, lean_object* v_k_1164_, lean_object* v_h_1165_, lean_object* v_acc_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1160_, v_inst_1161_, v_f_1162_, v_xs_1163_, v_k_1164_, v_acc_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM___redArg(lean_object* v_n_1170_, lean_object* v_inst_1171_, lean_object* v_f_1172_, lean_object* v_xs_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1176_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1170_, v_inst_1171_, v_f_1172_, v_xs_1173_, v___x_1174_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapM(lean_object* v_m_1177_, lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_n_1180_, lean_object* v_inst_1181_, lean_object* v_f_1182_, lean_object* v_xs_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1186_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___redArg(v_n_1180_, v_inst_1181_, v_f_1182_, v_xs_1183_, v___x_1184_, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg___lam__0(lean_object* v_f_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_apply_1(v_f_1187_, v___y_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Vector_forM___redArg(lean_object* v_inst_1191_, lean_object* v_xs_1192_, lean_object* v_f_1193_){
_start:
{
lean_object* v_toApplicative_1194_; lean_object* v_toPure_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_toApplicative_1194_ = lean_ctor_get(v_inst_1191_, 0);
v_toPure_1195_ = lean_ctor_get(v_toApplicative_1194_, 1);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_xs_1192_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_inc(v_toPure_1195_);
lean_dec(v_f_1193_);
lean_dec_ref(v_xs_1192_);
lean_dec_ref(v_inst_1191_);
v___x_1200_ = lean_apply_2(v_toPure_1195_, lean_box(0), v___x_1198_);
return v___x_1200_;
}
else
{
lean_object* v___f_1201_; uint8_t v___x_1202_; 
v___f_1201_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1201_, 0, v_f_1193_);
v___x_1202_ = lean_nat_dec_le(v___x_1197_, v___x_1197_);
if (v___x_1202_ == 0)
{
if (v___x_1199_ == 0)
{
lean_object* v___x_1203_; 
lean_inc(v_toPure_1195_);
lean_dec_ref(v___f_1201_);
lean_dec_ref(v_xs_1192_);
lean_dec_ref(v_inst_1191_);
v___x_1203_ = lean_apply_2(v_toPure_1195_, lean_box(0), v___x_1198_);
return v___x_1203_;
}
else
{
size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = lean_usize_of_nat(v___x_1197_);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1191_, v___f_1201_, v_xs_1192_, v___x_1204_, v___x_1205_, v___x_1198_);
return v___x_1206_;
}
}
else
{
size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_of_nat(v___x_1197_);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1191_, v___f_1201_, v_xs_1192_, v___x_1207_, v___x_1208_, v___x_1198_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM(lean_object* v_m_1210_, lean_object* v_00_u03b1_1211_, lean_object* v_n_1212_, lean_object* v_inst_1213_, lean_object* v_xs_1214_, lean_object* v_f_1215_){
_start:
{
lean_object* v_toApplicative_1216_; lean_object* v_toPure_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_toApplicative_1216_ = lean_ctor_get(v_inst_1213_, 0);
v_toPure_1217_ = lean_ctor_get(v_toApplicative_1216_, 1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_array_get_size(v_xs_1214_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_nat_dec_lt(v___x_1218_, v___x_1219_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_inc(v_toPure_1217_);
lean_dec(v_f_1215_);
lean_dec_ref(v_xs_1214_);
lean_dec_ref(v_inst_1213_);
v___x_1222_ = lean_apply_2(v_toPure_1217_, lean_box(0), v___x_1220_);
return v___x_1222_;
}
else
{
lean_object* v___f_1223_; uint8_t v___x_1224_; 
v___f_1223_ = lean_alloc_closure((void*)(l_Vector_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1223_, 0, v_f_1215_);
v___x_1224_ = lean_nat_dec_le(v___x_1219_, v___x_1219_);
if (v___x_1224_ == 0)
{
if (v___x_1221_ == 0)
{
lean_object* v___x_1225_; 
lean_inc(v_toPure_1217_);
lean_dec_ref(v___f_1223_);
lean_dec_ref(v_xs_1214_);
lean_dec_ref(v_inst_1213_);
v___x_1225_ = lean_apply_2(v_toPure_1217_, lean_box(0), v___x_1220_);
return v___x_1225_;
}
else
{
size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = ((size_t)0ULL);
v___x_1227_ = lean_usize_of_nat(v___x_1219_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1213_, v___f_1223_, v_xs_1214_, v___x_1226_, v___x_1227_, v___x_1220_);
return v___x_1228_;
}
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_of_nat(v___x_1219_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1213_, v___f_1223_, v_xs_1214_, v___x_1229_, v___x_1230_, v___x_1220_);
return v___x_1231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_forM___boxed(lean_object* v_m_1232_, lean_object* v_00_u03b1_1233_, lean_object* v_n_1234_, lean_object* v_inst_1235_, lean_object* v_xs_1236_, lean_object* v_f_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Vector_forM(v_m_1232_, v_00_u03b1_1233_, v_n_1234_, v_inst_1235_, v_xs_1236_, v_f_1237_);
lean_dec(v_n_1234_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed(lean_object* v_i_1239_, lean_object* v_acc_1240_, lean_object* v_n_1241_, lean_object* v_inst_1242_, lean_object* v_xs_1243_, lean_object* v_f_1244_, lean_object* v_____do__lift_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(v_i_1239_, v_acc_1240_, v_n_1241_, v_inst_1242_, v_xs_1243_, v_f_1244_, v_____do__lift_1245_);
lean_dec_ref(v_____do__lift_1245_);
lean_dec(v_i_1239_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(lean_object* v_n_1247_, lean_object* v_inst_1248_, lean_object* v_xs_1249_, lean_object* v_f_1250_, lean_object* v_i_1251_, lean_object* v_acc_1252_){
_start:
{
lean_object* v_toApplicative_1253_; lean_object* v_toBind_1254_; lean_object* v_toPure_1255_; uint8_t v___x_1256_; 
v_toApplicative_1253_ = lean_ctor_get(v_inst_1248_, 0);
v_toBind_1254_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc(v_toBind_1254_);
v_toPure_1255_ = lean_ctor_get(v_toApplicative_1253_, 1);
v___x_1256_ = lean_nat_dec_lt(v_i_1251_, v_n_1247_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_inc(v_toPure_1255_);
lean_dec(v_toBind_1254_);
lean_dec(v_i_1251_);
lean_dec(v_f_1250_);
lean_dec_ref(v_xs_1249_);
lean_dec_ref(v_inst_1248_);
lean_dec(v_n_1247_);
v___x_1257_ = lean_apply_2(v_toPure_1255_, lean_box(0), v_acc_1252_);
return v___x_1257_;
}
else
{
lean_object* v___f_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_inc(v_f_1250_);
lean_inc_ref(v_xs_1249_);
lean_inc(v_i_1251_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1258_, 0, v_i_1251_);
lean_closure_set(v___f_1258_, 1, v_acc_1252_);
lean_closure_set(v___f_1258_, 2, v_n_1247_);
lean_closure_set(v___f_1258_, 3, v_inst_1248_);
lean_closure_set(v___f_1258_, 4, v_xs_1249_);
lean_closure_set(v___f_1258_, 5, v_f_1250_);
v___x_1259_ = lean_array_fget(v_xs_1249_, v_i_1251_);
lean_dec(v_i_1251_);
lean_dec_ref(v_xs_1249_);
v___x_1260_ = lean_apply_1(v_f_1250_, v___x_1259_);
v___x_1261_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v___x_1260_, v___f_1258_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg___lam__0(lean_object* v_i_1262_, lean_object* v_acc_1263_, lean_object* v_n_1264_, lean_object* v_inst_1265_, lean_object* v_xs_1266_, lean_object* v_f_1267_, lean_object* v_____do__lift_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1269_ = lean_unsigned_to_nat(1u);
v___x_1270_ = lean_nat_add(v_i_1262_, v___x_1269_);
v___x_1271_ = l_Array_append___redArg(v_acc_1263_, v_____do__lift_1268_);
v___x_1272_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1264_, v_inst_1265_, v_xs_1266_, v_f_1267_, v___x_1270_, v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(lean_object* v_m_1273_, lean_object* v_00_u03b1_1274_, lean_object* v_n_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_k_1277_, lean_object* v_inst_1278_, lean_object* v_xs_1279_, lean_object* v_f_1280_, lean_object* v_i_1281_, lean_object* v_h_1282_, lean_object* v_acc_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1275_, v_inst_1278_, v_xs_1279_, v_f_1280_, v_i_1281_, v_acc_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___boxed(lean_object* v_m_1285_, lean_object* v_00_u03b1_1286_, lean_object* v_n_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_k_1289_, lean_object* v_inst_1290_, lean_object* v_xs_1291_, lean_object* v_f_1292_, lean_object* v_i_1293_, lean_object* v_h_1294_, lean_object* v_acc_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go(v_m_1285_, v_00_u03b1_1286_, v_n_1287_, v_00_u03b2_1288_, v_k_1289_, v_inst_1290_, v_xs_1291_, v_f_1292_, v_i_1293_, v_h_1294_, v_acc_1295_);
lean_dec(v_k_1289_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___redArg(lean_object* v_n_1297_, lean_object* v_inst_1298_, lean_object* v_xs_1299_, lean_object* v_f_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1303_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1297_, v_inst_1298_, v_xs_1299_, v_f_1300_, v___x_1301_, v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM(lean_object* v_m_1304_, lean_object* v_00_u03b1_1305_, lean_object* v_n_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_k_1308_, lean_object* v_inst_1309_, lean_object* v_xs_1310_, lean_object* v_f_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_unsigned_to_nat(0u);
v___x_1313_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1314_ = l___private_Init_Data_Vector_Basic_0__Vector_flatMapM_go___redArg(v_n_1306_, v_inst_1309_, v_xs_1310_, v_f_1311_, v___x_1312_, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMapM___boxed(lean_object* v_m_1315_, lean_object* v_00_u03b1_1316_, lean_object* v_n_1317_, lean_object* v_00_u03b2_1318_, lean_object* v_k_1319_, lean_object* v_inst_1320_, lean_object* v_xs_1321_, lean_object* v_f_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Vector_flatMapM(v_m_1315_, v_00_u03b1_1316_, v_n_1317_, v_00_u03b2_1318_, v_k_1319_, v_inst_1320_, v_xs_1321_, v_f_1322_);
lean_dec(v_k_1319_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0___boxed(lean_object* v_j_1324_, lean_object* v_ys_1325_, lean_object* v_inst_1326_, lean_object* v_xs_1327_, lean_object* v_f_1328_, lean_object* v_n_1329_, lean_object* v_____do__lift_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Vector_mapFinIdxM_map___redArg___lam__0(v_j_1324_, v_ys_1325_, v_inst_1326_, v_xs_1327_, v_f_1328_, v_n_1329_, v_____do__lift_1330_);
lean_dec(v_n_1329_);
lean_dec(v_j_1324_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg(lean_object* v_inst_1332_, lean_object* v_xs_1333_, lean_object* v_f_1334_, lean_object* v_i_1335_, lean_object* v_j_1336_, lean_object* v_ys_1337_){
_start:
{
lean_object* v_toApplicative_1338_; lean_object* v_toBind_1339_; lean_object* v_toPure_1340_; lean_object* v_zero_1341_; uint8_t v_isZero_1342_; 
v_toApplicative_1338_ = lean_ctor_get(v_inst_1332_, 0);
v_toBind_1339_ = lean_ctor_get(v_inst_1332_, 1);
lean_inc(v_toBind_1339_);
v_toPure_1340_ = lean_ctor_get(v_toApplicative_1338_, 1);
v_zero_1341_ = lean_unsigned_to_nat(0u);
v_isZero_1342_ = lean_nat_dec_eq(v_i_1335_, v_zero_1341_);
if (v_isZero_1342_ == 1)
{
lean_object* v___x_1343_; 
lean_inc(v_toPure_1340_);
lean_dec(v_toBind_1339_);
lean_dec(v_j_1336_);
lean_dec(v_f_1334_);
lean_dec_ref(v_xs_1333_);
lean_dec_ref(v_inst_1332_);
v___x_1343_ = lean_apply_2(v_toPure_1340_, lean_box(0), v_ys_1337_);
return v___x_1343_;
}
else
{
lean_object* v_one_1344_; lean_object* v_n_1345_; lean_object* v___f_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v_one_1344_ = lean_unsigned_to_nat(1u);
v_n_1345_ = lean_nat_sub(v_i_1335_, v_one_1344_);
lean_inc(v_f_1334_);
lean_inc_ref(v_xs_1333_);
lean_inc(v_j_1336_);
v___f_1346_ = lean_alloc_closure((void*)(l_Vector_mapFinIdxM_map___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1346_, 0, v_j_1336_);
lean_closure_set(v___f_1346_, 1, v_ys_1337_);
lean_closure_set(v___f_1346_, 2, v_inst_1332_);
lean_closure_set(v___f_1346_, 3, v_xs_1333_);
lean_closure_set(v___f_1346_, 4, v_f_1334_);
lean_closure_set(v___f_1346_, 5, v_n_1345_);
v___x_1347_ = lean_array_fget(v_xs_1333_, v_j_1336_);
lean_dec_ref(v_xs_1333_);
v___x_1348_ = lean_apply_3(v_f_1334_, v_j_1336_, v___x_1347_, lean_box(0));
v___x_1349_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1348_, v___f_1346_);
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___lam__0(lean_object* v_j_1350_, lean_object* v_ys_1351_, lean_object* v_inst_1352_, lean_object* v_xs_1353_, lean_object* v_f_1354_, lean_object* v_n_1355_, lean_object* v_____do__lift_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v_j_1350_, v___x_1357_);
v___x_1359_ = lean_array_push(v_ys_1351_, v_____do__lift_1356_);
v___x_1360_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1352_, v_xs_1353_, v_f_1354_, v_n_1355_, v___x_1358_, v___x_1359_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___redArg___boxed(lean_object* v_inst_1361_, lean_object* v_xs_1362_, lean_object* v_f_1363_, lean_object* v_i_1364_, lean_object* v_j_1365_, lean_object* v_ys_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1361_, v_xs_1362_, v_f_1363_, v_i_1364_, v_j_1365_, v_ys_1366_);
lean_dec(v_i_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map(lean_object* v_n_1368_, lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_m_1371_, lean_object* v_inst_1372_, lean_object* v_xs_1373_, lean_object* v_f_1374_, lean_object* v_i_1375_, lean_object* v_j_1376_, lean_object* v_inv_1377_, lean_object* v_ys_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1372_, v_xs_1373_, v_f_1374_, v_i_1375_, v_j_1376_, v_ys_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM_map___boxed(lean_object* v_n_1380_, lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_m_1383_, lean_object* v_inst_1384_, lean_object* v_xs_1385_, lean_object* v_f_1386_, lean_object* v_i_1387_, lean_object* v_j_1388_, lean_object* v_inv_1389_, lean_object* v_ys_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Vector_mapFinIdxM_map(v_n_1380_, v_00_u03b1_1381_, v_00_u03b2_1382_, v_m_1383_, v_inst_1384_, v_xs_1385_, v_f_1386_, v_i_1387_, v_j_1388_, v_inv_1389_, v_ys_1390_);
lean_dec(v_i_1387_);
lean_dec(v_n_1380_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg(lean_object* v_n_1392_, lean_object* v_inst_1393_, lean_object* v_xs_1394_, lean_object* v_f_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1398_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1393_, v_xs_1394_, v_f_1395_, v_n_1392_, v___x_1396_, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___redArg___boxed(lean_object* v_n_1399_, lean_object* v_inst_1400_, lean_object* v_xs_1401_, lean_object* v_f_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Vector_mapFinIdxM___redArg(v_n_1399_, v_inst_1400_, v_xs_1401_, v_f_1402_);
lean_dec(v_n_1399_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM(lean_object* v_n_1404_, lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_m_1407_, lean_object* v_inst_1408_, lean_object* v_xs_1409_, lean_object* v_f_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1413_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1408_, v_xs_1409_, v_f_1410_, v_n_1404_, v___x_1411_, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapFinIdxM___boxed(lean_object* v_n_1414_, lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_m_1417_, lean_object* v_inst_1418_, lean_object* v_xs_1419_, lean_object* v_f_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Vector_mapFinIdxM(v_n_1414_, v_00_u03b1_1415_, v_00_u03b2_1416_, v_m_1417_, v_inst_1418_, v_xs_1419_, v_f_1420_);
lean_dec(v_n_1414_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg(lean_object* v_n_1422_, lean_object* v_inst_1423_, lean_object* v_f_1424_, lean_object* v_xs_1425_){
_start:
{
lean_object* v___f_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___f_1426_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1426_, 0, v_f_1424_);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1429_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1423_, v_xs_1425_, v___f_1426_, v_n_1422_, v___x_1427_, v___x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___redArg___boxed(lean_object* v_n_1430_, lean_object* v_inst_1431_, lean_object* v_f_1432_, lean_object* v_xs_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Vector_mapIdxM___redArg(v_n_1430_, v_inst_1431_, v_f_1432_, v_xs_1433_);
lean_dec(v_n_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM(lean_object* v_n_1435_, lean_object* v_00_u03b1_1436_, lean_object* v_00_u03b2_1437_, lean_object* v_m_1438_, lean_object* v_inst_1439_, lean_object* v_f_1440_, lean_object* v_xs_1441_){
_start:
{
lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___f_1442_ = lean_alloc_closure((void*)(l_Vector_mapIdx___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1442_, 0, v_f_1440_);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1445_ = l_Vector_mapFinIdxM_map___redArg(v_inst_1439_, v_xs_1441_, v___f_1442_, v_n_1435_, v___x_1443_, v___x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Vector_mapIdxM___boxed(lean_object* v_n_1446_, lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_m_1449_, lean_object* v_inst_1450_, lean_object* v_f_1451_, lean_object* v_xs_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Vector_mapIdxM(v_n_1446_, v_00_u03b1_1447_, v_00_u03b2_1448_, v_m_1449_, v_inst_1450_, v_f_1451_, v_xs_1452_);
lean_dec(v_n_1446_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___redArg(lean_object* v_inst_1454_, lean_object* v_f_1455_, lean_object* v_xs_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1454_, v_f_1455_, v_xs_1456_, v___x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM(lean_object* v_00_u03b2_1459_, lean_object* v_n_1460_, lean_object* v_00_u03b1_1461_, lean_object* v_m_1462_, lean_object* v_inst_1463_, lean_object* v_f_1464_, lean_object* v_xs_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v_inst_1463_, v_f_1464_, v_xs_1465_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Vector_firstM___boxed(lean_object* v_00_u03b2_1468_, lean_object* v_n_1469_, lean_object* v_00_u03b1_1470_, lean_object* v_m_1471_, lean_object* v_inst_1472_, lean_object* v_f_1473_, lean_object* v_xs_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Vector_firstM(v_00_u03b2_1468_, v_n_1469_, v_00_u03b1_1470_, v_m_1471_, v_inst_1472_, v_f_1473_, v_xs_1474_);
lean_dec(v_n_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0(lean_object* v_x_1476_){
_start:
{
lean_inc_ref(v_x_1476_);
return v_x_1476_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg___lam__0___boxed(lean_object* v_x_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Vector_flatten___redArg___lam__0(v_x_1477_);
lean_dec_ref(v_x_1477_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___redArg(lean_object* v_xs_1483_){
_start:
{
lean_object* v___f_1484_; lean_object* v___x_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___f_1484_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1485_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1486_ = lean_array_size(v_xs_1483_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1485_, v___f_1484_, v_sz_1486_, v___x_1487_, v_xs_1483_);
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1491_ = lean_array_get_size(v___x_1488_);
v___x_1492_ = lean_nat_dec_lt(v___x_1489_, v___x_1491_);
if (v___x_1492_ == 0)
{
lean_dec(v___x_1488_);
return v___x_1490_;
}
else
{
lean_object* v___f_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v___f_1493_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1494_ = lean_usize_of_nat(v___x_1491_);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1485_, v___f_1493_, v___x_1488_, v___x_1487_, v___x_1494_, v___x_1490_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten(lean_object* v_00_u03b1_1496_, lean_object* v_n_1497_, lean_object* v_m_1498_, lean_object* v_xs_1499_){
_start:
{
lean_object* v___f_1500_; lean_object* v___x_1501_; size_t v_sz_1502_; size_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___f_1500_ = ((lean_object*)(l_Vector_flatten___redArg___closed__0));
v___x_1501_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v_sz_1502_ = lean_array_size(v_xs_1499_);
v___x_1503_ = ((size_t)0ULL);
v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1501_, v___f_1500_, v_sz_1502_, v___x_1503_, v_xs_1499_);
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1507_ = lean_array_get_size(v___x_1504_);
v___x_1508_ = lean_nat_dec_lt(v___x_1505_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec(v___x_1504_);
return v___x_1506_;
}
else
{
lean_object* v___f_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___f_1509_ = ((lean_object*)(l_Vector_flatten___redArg___closed__2));
v___x_1510_ = lean_usize_of_nat(v___x_1507_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1501_, v___f_1509_, v___x_1504_, v___x_1503_, v___x_1510_, v___x_1506_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatten___boxed(lean_object* v_00_u03b1_1512_, lean_object* v_n_1513_, lean_object* v_m_1514_, lean_object* v_xs_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Vector_flatten(v_00_u03b1_1512_, v_n_1513_, v_m_1514_, v_xs_1515_);
lean_dec(v_m_1514_);
lean_dec(v_n_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg___lam__0(lean_object* v_f_1517_, lean_object* v_x1_1518_, lean_object* v_x2_1519_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_apply_1(v_f_1517_, v_x2_1519_);
v___x_1521_ = l_Array_append___redArg(v_x1_1518_, v___x_1520_);
lean_dec_ref(v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___redArg(lean_object* v_xs_1522_, lean_object* v_f_1523_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1526_ = lean_array_get_size(v_xs_1522_);
v___x_1527_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1528_ = lean_nat_dec_lt(v___x_1524_, v___x_1526_);
if (v___x_1528_ == 0)
{
lean_dec_ref(v_f_1523_);
lean_dec_ref(v_xs_1522_);
return v___x_1525_;
}
else
{
lean_object* v___f_1529_; size_t v___x_1530_; size_t v___x_1531_; lean_object* v___x_1532_; 
v___f_1529_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1529_, 0, v_f_1523_);
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = lean_usize_of_nat(v___x_1526_);
v___x_1532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1527_, v___f_1529_, v_xs_1522_, v___x_1530_, v___x_1531_, v___x_1525_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap(lean_object* v_00_u03b1_1533_, lean_object* v_n_1534_, lean_object* v_00_u03b2_1535_, lean_object* v_m_1536_, lean_object* v_xs_1537_, lean_object* v_f_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = ((lean_object*)(l_Vector_flatten___redArg___closed__1));
v___x_1541_ = lean_array_get_size(v_xs_1537_);
v___x_1542_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1543_ = lean_nat_dec_lt(v___x_1539_, v___x_1541_);
if (v___x_1543_ == 0)
{
lean_dec_ref(v_f_1538_);
lean_dec_ref(v_xs_1537_);
return v___x_1540_;
}
else
{
lean_object* v___f_1544_; size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___f_1544_ = lean_alloc_closure((void*)(l_Vector_flatMap___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1544_, 0, v_f_1538_);
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1541_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1542_, v___f_1544_, v_xs_1537_, v___x_1545_, v___x_1546_, v___x_1540_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_flatMap___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_n_1549_, lean_object* v_00_u03b2_1550_, lean_object* v_m_1551_, lean_object* v_xs_1552_, lean_object* v_f_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Vector_flatMap(v_00_u03b1_1548_, v_n_1549_, v_00_u03b2_1550_, v_m_1551_, v_xs_1552_, v_f_1553_);
lean_dec(v_m_1551_);
lean_dec(v_n_1549_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg(lean_object* v_xs_1555_, lean_object* v_k_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Array_zipIdx___redArg(v_xs_1555_, v_k_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___redArg___boxed(lean_object* v_xs_1558_, lean_object* v_k_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Vector_zipIdx___redArg(v_xs_1558_, v_k_1559_);
lean_dec(v_k_1559_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx(lean_object* v_00_u03b1_1561_, lean_object* v_n_1562_, lean_object* v_xs_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Array_zipIdx___redArg(v_xs_1563_, v_k_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipIdx___boxed(lean_object* v_00_u03b1_1566_, lean_object* v_n_1567_, lean_object* v_xs_1568_, lean_object* v_k_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Vector_zipIdx(v_00_u03b1_1566_, v_n_1567_, v_xs_1568_, v_k_1569_);
lean_dec(v_k_1569_);
lean_dec(v_n_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg(lean_object* v_as_1571_, lean_object* v_bs_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Array_zip___redArg(v_as_1571_, v_bs_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___redArg___boxed(lean_object* v_as_1574_, lean_object* v_bs_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Vector_zip___redArg(v_as_1574_, v_bs_1575_);
lean_dec_ref(v_bs_1575_);
lean_dec_ref(v_as_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip(lean_object* v_00_u03b1_1577_, lean_object* v_n_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_as_1580_, lean_object* v_bs_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Array_zip___redArg(v_as_1580_, v_bs_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Vector_zip___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_n_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_as_1586_, lean_object* v_bs_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_Vector_zip(v_00_u03b1_1583_, v_n_1584_, v_00_u03b2_1585_, v_as_1586_, v_bs_1587_);
lean_dec_ref(v_bs_1587_);
lean_dec_ref(v_as_1586_);
lean_dec(v_n_1584_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___redArg(lean_object* v_f_1589_, lean_object* v_as_1590_, lean_object* v_bs_1591_){
_start:
{
lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___f_1592_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1592_, 0, v_f_1589_);
v___x_1593_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1596_ = l_Array_zipWithMAux___redArg(v___x_1593_, v_as_1590_, v_bs_1591_, v___f_1592_, v___x_1594_, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith(lean_object* v_00_u03b1_1597_, lean_object* v_00_u03b2_1598_, lean_object* v_00_u03c6_1599_, lean_object* v_n_1600_, lean_object* v_f_1601_, lean_object* v_as_1602_, lean_object* v_bs_1603_){
_start:
{
lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___f_1604_ = lean_alloc_closure((void*)(l_Vector_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1604_, 0, v_f_1601_);
v___x_1605_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = ((lean_object*)(l_Vector_mapM___redArg___closed__0));
v___x_1608_ = l_Array_zipWithMAux___redArg(v___x_1605_, v_as_1602_, v_bs_1603_, v___f_1604_, v___x_1606_, v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Vector_zipWith___boxed(lean_object* v_00_u03b1_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_00_u03c6_1611_, lean_object* v_n_1612_, lean_object* v_f_1613_, lean_object* v_as_1614_, lean_object* v_bs_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Vector_zipWith(v_00_u03b1_1609_, v_00_u03b2_1610_, v_00_u03c6_1611_, v_n_1612_, v_f_1613_, v_as_1614_, v_bs_1615_);
lean_dec(v_n_1612_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg(lean_object* v_xs_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v_fst_1619_; lean_object* v_snd_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v___x_1618_ = l_Array_unzip___redArg(v_xs_1617_);
v_fst_1619_ = lean_ctor_get(v___x_1618_, 0);
v_snd_1620_ = lean_ctor_get(v___x_1618_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1618_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snd_1620_);
lean_inc(v_fst_1619_);
lean_dec(v___x_1618_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_fst_1619_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_snd_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___redArg___boxed(lean_object* v_xs_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Vector_unzip___redArg(v_xs_1628_);
lean_dec_ref(v_xs_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Vector_unzip(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_n_1632_, lean_object* v_xs_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v_fst_1635_; lean_object* v_snd_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v___x_1634_ = l_Array_unzip___redArg(v_xs_1633_);
v_fst_1635_ = lean_ctor_get(v___x_1634_, 0);
v_snd_1636_ = lean_ctor_get(v___x_1634_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1634_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_snd_1636_);
lean_inc(v_fst_1635_);
lean_dec(v___x_1634_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_fst_1635_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_snd_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_unzip___boxed(lean_object* v_00_u03b1_1644_, lean_object* v_00_u03b2_1645_, lean_object* v_n_1646_, lean_object* v_xs_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Vector_unzip(v_00_u03b1_1644_, v_00_u03b2_1645_, v_n_1646_, v_xs_1647_);
lean_dec_ref(v_xs_1647_);
lean_dec(v_n_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn___redArg(lean_object* v_n_1649_, lean_object* v_f_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Array_ofFn___redArg(v_n_1649_, v_f_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Vector_ofFn(lean_object* v_n_1652_, lean_object* v_00_u03b1_1653_, lean_object* v_f_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Array_ofFn___redArg(v_n_1652_, v_f_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Vector_swap___auto__1(void){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1656_;
}
}
static lean_object* _init_l_Vector_swap___auto__3(void){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg(lean_object* v_xs_1658_, lean_object* v_i_1659_, lean_object* v_j_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_array_fswap(v_xs_1658_, v_i_1659_, v_j_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___redArg___boxed(lean_object* v_xs_1662_, lean_object* v_i_1663_, lean_object* v_j_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Vector_swap___redArg(v_xs_1662_, v_i_1663_, v_j_1664_);
lean_dec(v_j_1664_);
lean_dec(v_i_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap(lean_object* v_00_u03b1_1666_, lean_object* v_n_1667_, lean_object* v_xs_1668_, lean_object* v_i_1669_, lean_object* v_j_1670_, lean_object* v_hi_1671_, lean_object* v_hj_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_array_fswap(v_xs_1668_, v_i_1669_, v_j_1670_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Vector_swap___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_n_1675_, lean_object* v_xs_1676_, lean_object* v_i_1677_, lean_object* v_j_1678_, lean_object* v_hi_1679_, lean_object* v_hj_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Vector_swap(v_00_u03b1_1674_, v_n_1675_, v_xs_1676_, v_i_1677_, v_j_1678_, v_hi_1679_, v_hj_1680_);
lean_dec(v_j_1678_);
lean_dec(v_i_1677_);
lean_dec(v_n_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg(lean_object* v_xs_1682_, lean_object* v_i_1683_, lean_object* v_j_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_array_swap(v_xs_1682_, v_i_1683_, v_j_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___redArg___boxed(lean_object* v_xs_1686_, lean_object* v_i_1687_, lean_object* v_j_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Vector_swapIfInBounds___redArg(v_xs_1686_, v_i_1687_, v_j_1688_);
lean_dec(v_j_1688_);
lean_dec(v_i_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds(lean_object* v_00_u03b1_1690_, lean_object* v_n_1691_, lean_object* v_xs_1692_, lean_object* v_i_1693_, lean_object* v_j_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_array_swap(v_xs_1692_, v_i_1693_, v_j_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapIfInBounds___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_n_1697_, lean_object* v_xs_1698_, lean_object* v_i_1699_, lean_object* v_j_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Vector_swapIfInBounds(v_00_u03b1_1696_, v_n_1697_, v_xs_1698_, v_i_1699_, v_j_1700_);
lean_dec(v_j_1700_);
lean_dec(v_i_1699_);
lean_dec(v_n_1697_);
return v_res_1701_;
}
}
static lean_object* _init_l_Vector_swapAt___auto__1(void){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg(lean_object* v_xs_1703_, lean_object* v_i_1704_, lean_object* v_x_1705_){
_start:
{
lean_object* v_e_1706_; lean_object* v_xs_x27_1707_; lean_object* v___x_1708_; 
v_e_1706_ = lean_array_fget(v_xs_1703_, v_i_1704_);
v_xs_x27_1707_ = lean_array_fset(v_xs_1703_, v_i_1704_, v_x_1705_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_e_1706_);
lean_ctor_set(v___x_1708_, 1, v_xs_x27_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___redArg___boxed(lean_object* v_xs_1709_, lean_object* v_i_1710_, lean_object* v_x_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Vector_swapAt___redArg(v_xs_1709_, v_i_1710_, v_x_1711_);
lean_dec(v_i_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt(lean_object* v_00_u03b1_1713_, lean_object* v_n_1714_, lean_object* v_xs_1715_, lean_object* v_i_1716_, lean_object* v_x_1717_, lean_object* v_hi_1718_){
_start:
{
lean_object* v_e_1719_; lean_object* v_xs_x27_1720_; lean_object* v___x_1721_; 
v_e_1719_ = lean_array_fget(v_xs_1715_, v_i_1716_);
v_xs_x27_1720_ = lean_array_fset(v_xs_1715_, v_i_1716_, v_x_1717_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v_e_1719_);
lean_ctor_set(v___x_1721_, 1, v_xs_x27_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_n_1723_, lean_object* v_xs_1724_, lean_object* v_i_1725_, lean_object* v_x_1726_, lean_object* v_hi_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Vector_swapAt(v_00_u03b1_1722_, v_n_1723_, v_xs_1724_, v_i_1725_, v_x_1726_, v_hi_1727_);
lean_dec(v_i_1725_);
lean_dec(v_n_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___redArg(lean_object* v_xs_1733_, lean_object* v_i_1734_, lean_object* v_x_1735_){
_start:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_array_get_size(v_xs_1733_);
v___x_1737_ = lean_nat_dec_lt(v_i_1734_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v_this_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v_this_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1738_, 0, v_x_1735_);
lean_ctor_set(v_this_1738_, 1, v_xs_1733_);
v___x_1739_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1740_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1741_ = lean_unsigned_to_nat(438u);
v___x_1742_ = lean_unsigned_to_nat(4u);
v___x_1743_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1744_ = l_Nat_reprFast(v_i_1734_);
v___x_1745_ = lean_string_append(v___x_1743_, v___x_1744_);
lean_dec_ref(v___x_1744_);
v___x_1746_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
v___x_1748_ = l_mkPanicMessageWithDecl(v___x_1739_, v___x_1740_, v___x_1741_, v___x_1742_, v___x_1747_);
lean_dec_ref(v___x_1747_);
v___x_1749_ = l_panic___redArg(v_this_1738_, v___x_1748_);
lean_dec_ref_known(v_this_1738_, 2);
v_fst_1750_ = lean_ctor_get(v___x_1749_, 0);
v_snd_1751_ = lean_ctor_get(v___x_1749_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1749_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snd_1751_);
lean_inc(v_fst_1750_);
lean_dec(v___x_1749_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_fst_1750_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_snd_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_e_1759_; lean_object* v_xs_x27_1760_; lean_object* v___x_1761_; 
v_e_1759_ = lean_array_fget(v_xs_1733_, v_i_1734_);
v_xs_x27_1760_ = lean_array_fset(v_xs_1733_, v_i_1734_, v_x_1735_);
lean_dec(v_i_1734_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_e_1759_);
lean_ctor_set(v___x_1761_, 1, v_xs_x27_1760_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21(lean_object* v_00_u03b1_1762_, lean_object* v_n_1763_, lean_object* v_xs_1764_, lean_object* v_i_1765_, lean_object* v_x_1766_){
_start:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = lean_array_get_size(v_xs_1764_);
v___x_1768_ = lean_nat_dec_lt(v_i_1765_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v_this_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v_fst_1781_; lean_object* v_snd_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_this_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_this_1769_, 0, v_x_1766_);
lean_ctor_set(v_this_1769_, 1, v_xs_1764_);
v___x_1770_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__0));
v___x_1771_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__1));
v___x_1772_ = lean_unsigned_to_nat(438u);
v___x_1773_ = lean_unsigned_to_nat(4u);
v___x_1774_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__2));
v___x_1775_ = l_Nat_reprFast(v_i_1765_);
v___x_1776_ = lean_string_append(v___x_1774_, v___x_1775_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = ((lean_object*)(l_Vector_swapAt_x21___redArg___closed__3));
v___x_1778_ = lean_string_append(v___x_1776_, v___x_1777_);
v___x_1779_ = l_mkPanicMessageWithDecl(v___x_1770_, v___x_1771_, v___x_1772_, v___x_1773_, v___x_1778_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = l_panic___redArg(v_this_1769_, v___x_1779_);
lean_dec_ref_known(v_this_1769_, 2);
v_fst_1781_ = lean_ctor_get(v___x_1780_, 0);
v_snd_1782_ = lean_ctor_get(v___x_1780_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_snd_1782_);
lean_inc(v_fst_1781_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_fst_1781_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_snd_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
else
{
lean_object* v_e_1790_; lean_object* v_xs_x27_1791_; lean_object* v___x_1792_; 
v_e_1790_ = lean_array_fget(v_xs_1764_, v_i_1765_);
v_xs_x27_1791_ = lean_array_fset(v_xs_1764_, v_i_1765_, v_x_1766_);
lean_dec(v_i_1765_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_e_1790_);
lean_ctor_set(v___x_1792_, 1, v_xs_x27_1791_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_swapAt_x21___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_n_1794_, lean_object* v_xs_1795_, lean_object* v_i_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Vector_swapAt_x21(v_00_u03b1_1793_, v_n_1794_, v_xs_1795_, v_i_1796_, v_x_1797_);
lean_dec(v_n_1794_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Vector_range(lean_object* v_n_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Array_range(v_n_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Vector_range_x27(lean_object* v_start_1801_, lean_object* v_size_1802_, lean_object* v_step_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Array_range_x27(v_start_1801_, v_size_1802_, v_step_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv___redArg(lean_object* v_n_1805_, lean_object* v_xs_1806_, lean_object* v_ys_1807_, lean_object* v_r_1808_){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Array_isEqvAux___redArg(v_xs_1806_, v_ys_1807_, v_r_1808_, v_n_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___redArg___boxed(lean_object* v_n_1810_, lean_object* v_xs_1811_, lean_object* v_ys_1812_, lean_object* v_r_1813_){
_start:
{
uint8_t v_res_1814_; lean_object* v_r_1815_; 
v_res_1814_ = l_Vector_isEqv___redArg(v_n_1810_, v_xs_1811_, v_ys_1812_, v_r_1813_);
lean_dec_ref(v_ys_1812_);
lean_dec_ref(v_xs_1811_);
v_r_1815_ = lean_box(v_res_1814_);
return v_r_1815_;
}
}
LEAN_EXPORT uint8_t l_Vector_isEqv(lean_object* v_00_u03b1_1816_, lean_object* v_n_1817_, lean_object* v_xs_1818_, lean_object* v_ys_1819_, lean_object* v_r_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Array_isEqvAux___redArg(v_xs_1818_, v_ys_1819_, v_r_1820_, v_n_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Vector_isEqv___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_n_1823_, lean_object* v_xs_1824_, lean_object* v_ys_1825_, lean_object* v_r_1826_){
_start:
{
uint8_t v_res_1827_; lean_object* v_r_1828_; 
v_res_1827_ = l_Vector_isEqv(v_00_u03b1_1822_, v_n_1823_, v_xs_1824_, v_ys_1825_, v_r_1826_);
lean_dec_ref(v_ys_1825_);
lean_dec_ref(v_xs_1824_);
v_r_1828_ = lean_box(v_res_1827_);
return v_r_1828_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__0(lean_object* v_inst_1829_, lean_object* v_x1_1830_, lean_object* v_x2_1831_){
_start:
{
lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1832_ = lean_apply_2(v_inst_1829_, v_x1_1830_, v_x2_1831_);
v___x_1833_ = lean_unbox(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__0___boxed(lean_object* v_inst_1834_, lean_object* v_x1_1835_, lean_object* v_x2_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Vector_instBEq___redArg___lam__0(v_inst_1834_, v_x1_1835_, v_x2_1836_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT uint8_t l_Vector_instBEq___redArg___lam__1(lean_object* v___f_1839_, lean_object* v_n_1840_, lean_object* v_xs_1841_, lean_object* v_ys_1842_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = l_Array_isEqvAux___redArg(v_xs_1841_, v_ys_1842_, v___f_1839_, v_n_1840_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg___lam__1___boxed(lean_object* v___f_1844_, lean_object* v_n_1845_, lean_object* v_xs_1846_, lean_object* v_ys_1847_){
_start:
{
uint8_t v_res_1848_; lean_object* v_r_1849_; 
v_res_1848_ = l_Vector_instBEq___redArg___lam__1(v___f_1844_, v_n_1845_, v_xs_1846_, v_ys_1847_);
lean_dec_ref(v_ys_1847_);
lean_dec_ref(v_xs_1846_);
v_r_1849_ = lean_box(v_res_1848_);
return v_r_1849_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq___redArg(lean_object* v_n_1850_, lean_object* v_inst_1851_){
_start:
{
lean_object* v___f_1852_; lean_object* v___f_1853_; 
v___f_1852_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1852_, 0, v_inst_1851_);
v___f_1853_ = lean_alloc_closure((void*)(l_Vector_instBEq___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1853_, 0, v___f_1852_);
lean_closure_set(v___f_1853_, 1, v_n_1850_);
return v___f_1853_;
}
}
LEAN_EXPORT lean_object* l_Vector_instBEq(lean_object* v_00_u03b1_1854_, lean_object* v_n_1855_, lean_object* v_inst_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Vector_instBEq___redArg(v_n_1855_, v_inst_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___redArg(lean_object* v_xs_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Array_reverse___redArg(v_xs_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse(lean_object* v_00_u03b1_1860_, lean_object* v_n_1861_, lean_object* v_xs_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Array_reverse___redArg(v_xs_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Vector_reverse___boxed(lean_object* v_00_u03b1_1864_, lean_object* v_n_1865_, lean_object* v_xs_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Vector_reverse(v_00_u03b1_1864_, v_n_1865_, v_xs_1866_);
lean_dec(v_n_1865_);
return v_res_1867_;
}
}
static lean_object* _init_l_Vector_eraseIdx___auto__1(void){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___redArg(lean_object* v_xs_1869_, lean_object* v_i_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Array_eraseIdx___redArg(v_xs_1869_, v_i_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx(lean_object* v_00_u03b1_1872_, lean_object* v_n_1873_, lean_object* v_xs_1874_, lean_object* v_i_1875_, lean_object* v_h_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Array_eraseIdx___redArg(v_xs_1874_, v_i_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx___boxed(lean_object* v_00_u03b1_1878_, lean_object* v_n_1879_, lean_object* v_xs_1880_, lean_object* v_i_1881_, lean_object* v_h_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Vector_eraseIdx(v_00_u03b1_1878_, v_n_1879_, v_xs_1880_, v_i_1881_, v_h_1882_);
lean_dec(v_n_1879_);
return v_res_1883_;
}
}
static lean_object* _init_l_Vector_eraseIdx_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1887_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1888_ = lean_unsigned_to_nat(4u);
v___x_1889_ = lean_unsigned_to_nat(395u);
v___x_1890_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__1));
v___x_1891_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1892_ = l_mkPanicMessageWithDecl(v___x_1891_, v___x_1890_, v___x_1889_, v___x_1888_, v___x_1887_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg(lean_object* v_n_1893_, lean_object* v_xs_1894_, lean_object* v_i_1895_){
_start:
{
uint8_t v___x_1896_; 
v___x_1896_ = lean_nat_dec_lt(v_i_1895_, v_n_1893_);
if (v___x_1896_ == 0)
{
lean_object* v_this_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_i_1895_);
v_this_1897_ = lean_array_pop(v_xs_1894_);
v___x_1898_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1899_ = l_panic___redArg(v_this_1897_, v___x_1898_);
lean_dec_ref(v_this_1897_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Array_eraseIdx___redArg(v_xs_1894_, v_i_1895_);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___redArg___boxed(lean_object* v_n_1901_, lean_object* v_xs_1902_, lean_object* v_i_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Vector_eraseIdx_x21___redArg(v_n_1901_, v_xs_1902_, v_i_1903_);
lean_dec(v_n_1901_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21(lean_object* v_00_u03b1_1905_, lean_object* v_n_1906_, lean_object* v_xs_1907_, lean_object* v_i_1908_){
_start:
{
uint8_t v___x_1909_; 
v___x_1909_ = lean_nat_dec_lt(v_i_1908_, v_n_1906_);
if (v___x_1909_ == 0)
{
lean_object* v_this_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec(v_i_1908_);
v_this_1910_ = lean_array_pop(v_xs_1907_);
v___x_1911_ = lean_obj_once(&l_Vector_eraseIdx_x21___redArg___closed__3, &l_Vector_eraseIdx_x21___redArg___closed__3_once, _init_l_Vector_eraseIdx_x21___redArg___closed__3);
v___x_1912_ = l_panic___redArg(v_this_1910_, v___x_1911_);
lean_dec_ref(v_this_1910_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Array_eraseIdx___redArg(v_xs_1907_, v_i_1908_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_eraseIdx_x21___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_n_1915_, lean_object* v_xs_1916_, lean_object* v_i_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Vector_eraseIdx_x21(v_00_u03b1_1914_, v_n_1915_, v_xs_1916_, v_i_1917_);
lean_dec(v_n_1915_);
return v_res_1918_;
}
}
static lean_object* _init_l_Vector_insertIdx___auto__1(void){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_obj_once(&l_Vector_set___auto__1___closed__17, &l_Vector_set___auto__1___closed__17_once, _init_l_Vector_set___auto__1___closed__17);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg(lean_object* v_xs_1920_, lean_object* v_i_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v_j_1923_; lean_object* v_as_1924_; lean_object* v___x_1925_; 
v_j_1923_ = lean_array_get_size(v_xs_1920_);
v_as_1924_ = lean_array_push(v_xs_1920_, v_x_1922_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1921_, v_as_1924_, v_j_1923_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___redArg___boxed(lean_object* v_xs_1926_, lean_object* v_i_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Vector_insertIdx___redArg(v_xs_1926_, v_i_1927_, v_x_1928_);
lean_dec(v_i_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx(lean_object* v_00_u03b1_1930_, lean_object* v_n_1931_, lean_object* v_xs_1932_, lean_object* v_i_1933_, lean_object* v_x_1934_, lean_object* v_h_1935_){
_start:
{
lean_object* v_j_1936_; lean_object* v_as_1937_; lean_object* v___x_1938_; 
v_j_1936_ = lean_array_get_size(v_xs_1932_);
v_as_1937_ = lean_array_push(v_xs_1932_, v_x_1934_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1933_, v_as_1937_, v_j_1936_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx___boxed(lean_object* v_00_u03b1_1939_, lean_object* v_n_1940_, lean_object* v_xs_1941_, lean_object* v_i_1942_, lean_object* v_x_1943_, lean_object* v_h_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Vector_insertIdx(v_00_u03b1_1939_, v_n_1940_, v_xs_1941_, v_i_1942_, v_x_1943_, v_h_1944_);
lean_dec(v_i_1942_);
lean_dec(v_n_1940_);
return v_res_1945_;
}
}
static lean_object* _init_l_Vector_insertIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1947_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__2));
v___x_1948_ = lean_unsigned_to_nat(4u);
v___x_1949_ = lean_unsigned_to_nat(408u);
v___x_1950_ = ((lean_object*)(l_Vector_insertIdx_x21___redArg___closed__0));
v___x_1951_ = ((lean_object*)(l_Vector_eraseIdx_x21___redArg___closed__0));
v___x_1952_ = l_mkPanicMessageWithDecl(v___x_1951_, v___x_1950_, v___x_1949_, v___x_1948_, v___x_1947_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg(lean_object* v_n_1953_, lean_object* v_xs_1954_, lean_object* v_i_1955_, lean_object* v_x_1956_){
_start:
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_nat_dec_le(v_i_1955_, v_n_1953_);
if (v___x_1957_ == 0)
{
lean_object* v_this_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_this_1958_ = lean_array_push(v_xs_1954_, v_x_1956_);
v___x_1959_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1960_ = l_panic___redArg(v_this_1958_, v___x_1959_);
lean_dec_ref(v_this_1958_);
return v___x_1960_;
}
else
{
lean_object* v_j_1961_; lean_object* v_as_1962_; lean_object* v___x_1963_; 
v_j_1961_ = lean_array_get_size(v_xs_1954_);
v_as_1962_ = lean_array_push(v_xs_1954_, v_x_1956_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1955_, v_as_1962_, v_j_1961_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___redArg___boxed(lean_object* v_n_1964_, lean_object* v_xs_1965_, lean_object* v_i_1966_, lean_object* v_x_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Vector_insertIdx_x21___redArg(v_n_1964_, v_xs_1965_, v_i_1966_, v_x_1967_);
lean_dec(v_i_1966_);
lean_dec(v_n_1964_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21(lean_object* v_00_u03b1_1969_, lean_object* v_n_1970_, lean_object* v_xs_1971_, lean_object* v_i_1972_, lean_object* v_x_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_nat_dec_le(v_i_1972_, v_n_1970_);
if (v___x_1974_ == 0)
{
lean_object* v_this_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_this_1975_ = lean_array_push(v_xs_1971_, v_x_1973_);
v___x_1976_ = lean_obj_once(&l_Vector_insertIdx_x21___redArg___closed__1, &l_Vector_insertIdx_x21___redArg___closed__1_once, _init_l_Vector_insertIdx_x21___redArg___closed__1);
v___x_1977_ = l_panic___redArg(v_this_1975_, v___x_1976_);
lean_dec_ref(v_this_1975_);
return v___x_1977_;
}
else
{
lean_object* v_j_1978_; lean_object* v_as_1979_; lean_object* v___x_1980_; 
v_j_1978_ = lean_array_get_size(v_xs_1971_);
v_as_1979_ = lean_array_push(v_xs_1971_, v_x_1973_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v_i_1972_, v_as_1979_, v_j_1978_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_insertIdx_x21___boxed(lean_object* v_00_u03b1_1981_, lean_object* v_n_1982_, lean_object* v_xs_1983_, lean_object* v_i_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Vector_insertIdx_x21(v_00_u03b1_1981_, v_n_1982_, v_xs_1983_, v_i_1984_, v_x_1985_);
lean_dec(v_i_1984_);
lean_dec(v_n_1982_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg(lean_object* v_n_1987_, lean_object* v_xs_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = l_Array_extract___redArg(v_xs_1988_, v___x_1989_, v_n_1987_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___redArg___boxed(lean_object* v_n_1991_, lean_object* v_xs_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Vector_tail___redArg(v_n_1991_, v_xs_1992_);
lean_dec_ref(v_xs_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail(lean_object* v_00_u03b1_1994_, lean_object* v_n_1995_, lean_object* v_xs_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = l_Array_extract___redArg(v_xs_1996_, v___x_1997_, v_n_1995_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Vector_tail___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_n_2000_, lean_object* v_xs_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Vector_tail(v_00_u03b1_1999_, v_n_2000_, v_xs_2001_);
lean_dec_ref(v_xs_2001_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg(lean_object* v_inst_2003_, lean_object* v_xs_2004_, lean_object* v_x_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Array_finIdxOf_x3f___redArg(v_inst_2003_, v_xs_2004_, v_x_2005_);
if (lean_obj_tag(v___x_2006_) == 0)
{
return v___x_2006_;
}
else
{
lean_object* v_val_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2014_; 
v_val_2007_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2009_ = v___x_2006_;
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_val_2007_);
lean_dec(v___x_2006_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2014_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2012_; 
if (v_isShared_2010_ == 0)
{
v___x_2012_ = v___x_2009_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v_val_2007_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___redArg___boxed(lean_object* v_inst_2015_, lean_object* v_xs_2016_, lean_object* v_x_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Vector_finIdxOf_x3f___redArg(v_inst_2015_, v_xs_2016_, v_x_2017_);
lean_dec_ref(v_xs_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f(lean_object* v_00_u03b1_2019_, lean_object* v_n_2020_, lean_object* v_inst_2021_, lean_object* v_xs_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Array_finIdxOf_x3f___redArg(v_inst_2021_, v_xs_2022_, v_x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
return v___x_2024_;
}
else
{
lean_object* v_val_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_val_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_val_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_val_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_finIdxOf_x3f___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_n_2034_, lean_object* v_inst_2035_, lean_object* v_xs_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Vector_finIdxOf_x3f(v_00_u03b1_2033_, v_n_2034_, v_inst_2035_, v_xs_2036_, v_x_2037_);
lean_dec_ref(v_xs_2036_);
lean_dec(v_n_2034_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg(lean_object* v_p_2039_, lean_object* v_xs_2040_){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_unsigned_to_nat(0u);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2039_, v_xs_2040_, v___x_2041_);
if (lean_obj_tag(v___x_2042_) == 0)
{
return v___x_2042_;
}
else
{
lean_object* v_val_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_val_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_val_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_val_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___redArg___boxed(lean_object* v_p_2051_, lean_object* v_xs_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Vector_findFinIdx_x3f___redArg(v_p_2051_, v_xs_2052_);
lean_dec_ref(v_xs_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f(lean_object* v_00_u03b1_2054_, lean_object* v_n_2055_, lean_object* v_p_2056_, lean_object* v_xs_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v_p_2056_, v_xs_2057_, v___x_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
return v___x_2059_;
}
else
{
lean_object* v_val_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
v_val_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_val_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_val_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_findFinIdx_x3f___boxed(lean_object* v_00_u03b1_2068_, lean_object* v_n_2069_, lean_object* v_p_2070_, lean_object* v_xs_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Vector_findFinIdx_x3f(v_00_u03b1_2068_, v_n_2069_, v_p_2070_, v_xs_2071_);
lean_dec_ref(v_xs_2071_);
lean_dec(v_n_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__0(lean_object* v_toPure_2073_, lean_object* v_____s_2074_){
_start:
{
lean_object* v_fst_2075_; 
v_fst_2075_ = lean_ctor_get(v_____s_2074_, 0);
lean_inc(v_fst_2075_);
lean_dec_ref(v_____s_2074_);
if (lean_obj_tag(v_fst_2075_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_apply_2(v_toPure_2073_, lean_box(0), v___x_2076_);
return v___x_2077_;
}
else
{
lean_object* v_val_2078_; lean_object* v___x_2079_; 
v_val_2078_ = lean_ctor_get(v_fst_2075_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v_fst_2075_, 1);
v___x_2079_ = lean_apply_2(v_toPure_2073_, lean_box(0), v_val_2078_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1(lean_object* v___x_2080_, lean_object* v_toPure_2081_, lean_object* v_a_2082_, lean_object* v___x_2083_, uint8_t v_____do__lift_2084_){
_start:
{
if (v_____do__lift_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v_a_2082_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2080_);
v___x_2086_ = lean_apply_2(v_toPure_2081_, lean_box(0), v___x_2085_);
return v___x_2086_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec_ref(v___x_2080_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_a_2082_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2083_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
v___x_2091_ = lean_apply_2(v_toPure_2081_, lean_box(0), v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__1___boxed(lean_object* v___x_2092_, lean_object* v_toPure_2093_, lean_object* v_a_2094_, lean_object* v___x_2095_, lean_object* v_____do__lift_2096_){
_start:
{
uint8_t v_____do__lift_124__boxed_2097_; lean_object* v_res_2098_; 
v_____do__lift_124__boxed_2097_ = lean_unbox(v_____do__lift_2096_);
v_res_2098_ = l_Vector_findM_x3f___redArg___lam__1(v___x_2092_, v_toPure_2093_, v_a_2094_, v___x_2095_, v_____do__lift_124__boxed_2097_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2(lean_object* v___x_2099_, lean_object* v_toPure_2100_, lean_object* v___x_2101_, lean_object* v_f_2102_, lean_object* v_toBind_2103_, lean_object* v_a_2104_, lean_object* v_x_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
lean_inc(v_a_2104_);
v___f_2107_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2107_, 0, v___x_2099_);
lean_closure_set(v___f_2107_, 1, v_toPure_2100_);
lean_closure_set(v___f_2107_, 2, v_a_2104_);
lean_closure_set(v___f_2107_, 3, v___x_2101_);
v___x_2108_ = lean_apply_1(v_f_2102_, v_a_2104_);
v___x_2109_ = lean_apply_4(v_toBind_2103_, lean_box(0), lean_box(0), v___x_2108_, v___f_2107_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg___lam__2___boxed(lean_object* v___x_2110_, lean_object* v_toPure_2111_, lean_object* v___x_2112_, lean_object* v_f_2113_, lean_object* v_toBind_2114_, lean_object* v_a_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Vector_findM_x3f___redArg___lam__2(v___x_2110_, v_toPure_2111_, v___x_2112_, v_f_2113_, v_toBind_2114_, v_a_2115_, v_x_2116_, v___y_2117_);
lean_dec_ref(v___y_2117_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___redArg(lean_object* v_inst_2122_, lean_object* v_f_2123_, lean_object* v_as_2124_){
_start:
{
lean_object* v_toApplicative_2125_; lean_object* v_toBind_2126_; lean_object* v_toPure_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; lean_object* v___f_2131_; size_t v_sz_2132_; size_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_toApplicative_2125_ = lean_ctor_get(v_inst_2122_, 0);
v_toBind_2126_ = lean_ctor_get(v_inst_2122_, 1);
lean_inc_n(v_toBind_2126_, 2);
v_toPure_2127_ = lean_ctor_get(v_toApplicative_2125_, 1);
v___x_2128_ = lean_box(0);
v___x_2129_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2127_, 2);
v___f_2130_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2130_, 0, v_toPure_2127_);
v___f_2131_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2131_, 0, v___x_2129_);
lean_closure_set(v___f_2131_, 1, v_toPure_2127_);
lean_closure_set(v___f_2131_, 2, v___x_2128_);
lean_closure_set(v___f_2131_, 3, v_f_2123_);
lean_closure_set(v___f_2131_, 4, v_toBind_2126_);
v_sz_2132_ = lean_array_size(v_as_2124_);
v___x_2133_ = ((size_t)0ULL);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2122_, v_as_2124_, v___f_2131_, v_sz_2132_, v___x_2133_, v___x_2129_);
v___x_2135_ = lean_apply_4(v_toBind_2126_, lean_box(0), lean_box(0), v___x_2134_, v___f_2130_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f(lean_object* v_n_2136_, lean_object* v_00_u03b1_2137_, lean_object* v_m_2138_, lean_object* v_inst_2139_, lean_object* v_f_2140_, lean_object* v_as_2141_){
_start:
{
lean_object* v_toApplicative_2142_; lean_object* v_toBind_2143_; lean_object* v_toPure_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___f_2147_; lean_object* v___f_2148_; size_t v_sz_2149_; size_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_toApplicative_2142_ = lean_ctor_get(v_inst_2139_, 0);
v_toBind_2143_ = lean_ctor_get(v_inst_2139_, 1);
lean_inc_n(v_toBind_2143_, 2);
v_toPure_2144_ = lean_ctor_get(v_toApplicative_2142_, 1);
v___x_2145_ = lean_box(0);
v___x_2146_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2144_, 2);
v___f_2147_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2147_, 0, v_toPure_2144_);
v___f_2148_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_2148_, 0, v___x_2146_);
lean_closure_set(v___f_2148_, 1, v_toPure_2144_);
lean_closure_set(v___f_2148_, 2, v___x_2145_);
lean_closure_set(v___f_2148_, 3, v_f_2140_);
lean_closure_set(v___f_2148_, 4, v_toBind_2143_);
v_sz_2149_ = lean_array_size(v_as_2141_);
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2139_, v_as_2141_, v___f_2148_, v_sz_2149_, v___x_2150_, v___x_2146_);
v___x_2152_ = lean_apply_4(v_toBind_2143_, lean_box(0), lean_box(0), v___x_2151_, v___f_2147_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Vector_findM_x3f___boxed(lean_object* v_n_2153_, lean_object* v_00_u03b1_2154_, lean_object* v_m_2155_, lean_object* v_inst_2156_, lean_object* v_f_2157_, lean_object* v_as_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Vector_findM_x3f(v_n_2153_, v_00_u03b1_2154_, v_m_2155_, v_inst_2156_, v_f_2157_, v_as_2158_);
lean_dec(v_n_2153_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__1(lean_object* v___x_2160_, lean_object* v_toPure_2161_, lean_object* v___x_2162_, lean_object* v_____do__lift_2163_){
_start:
{
if (lean_obj_tag(v_____do__lift_2163_) == 1)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v___x_2162_);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_____do__lift_2163_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v___x_2160_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
v___x_2167_ = lean_apply_2(v_toPure_2161_, lean_box(0), v___x_2166_);
return v___x_2167_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v_____do__lift_2163_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2162_);
v___x_2169_ = lean_apply_2(v_toPure_2161_, lean_box(0), v___x_2168_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0(lean_object* v_f_2170_, lean_object* v_toBind_2171_, lean_object* v___f_2172_, lean_object* v_a_2173_, lean_object* v_x_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_apply_1(v_f_2170_, v_a_2173_);
v___x_2177_ = lean_apply_4(v_toBind_2171_, lean_box(0), lean_box(0), v___x_2176_, v___f_2172_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg___lam__0___boxed(lean_object* v_f_2178_, lean_object* v_toBind_2179_, lean_object* v___f_2180_, lean_object* v_a_2181_, lean_object* v_x_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Vector_findSomeM_x3f___redArg___lam__0(v_f_2178_, v_toBind_2179_, v___f_2180_, v_a_2181_, v_x_2182_, v___y_2183_);
lean_dec_ref(v___y_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___redArg(lean_object* v_inst_2185_, lean_object* v_f_2186_, lean_object* v_as_2187_){
_start:
{
lean_object* v_toApplicative_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; size_t v_sz_2196_; size_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2185_, 0);
v_toBind_2189_ = lean_ctor_get(v_inst_2185_, 1);
lean_inc_n(v_toBind_2189_, 2);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2188_, 1);
v___x_2191_ = lean_box(0);
v___x_2192_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2190_, 2);
v___f_2193_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2190_);
v___f_2194_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2194_, 0, v___x_2191_);
lean_closure_set(v___f_2194_, 1, v_toPure_2190_);
lean_closure_set(v___f_2194_, 2, v___x_2192_);
v___f_2195_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2195_, 0, v_f_2186_);
lean_closure_set(v___f_2195_, 1, v_toBind_2189_);
lean_closure_set(v___f_2195_, 2, v___f_2194_);
v_sz_2196_ = lean_array_size(v_as_2187_);
v___x_2197_ = ((size_t)0ULL);
v___x_2198_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2185_, v_as_2187_, v___f_2195_, v_sz_2196_, v___x_2197_, v___x_2192_);
v___x_2199_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v___x_2198_, v___f_2193_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f(lean_object* v_m_2200_, lean_object* v_00_u03b1_2201_, lean_object* v_00_u03b2_2202_, lean_object* v_n_2203_, lean_object* v_inst_2204_, lean_object* v_f_2205_, lean_object* v_as_2206_){
_start:
{
lean_object* v_toApplicative_2207_; lean_object* v_toBind_2208_; lean_object* v_toPure_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_toApplicative_2207_ = lean_ctor_get(v_inst_2204_, 0);
v_toBind_2208_ = lean_ctor_get(v_inst_2204_, 1);
lean_inc_n(v_toBind_2208_, 2);
v_toPure_2209_ = lean_ctor_get(v_toApplicative_2207_, 1);
v___x_2210_ = lean_box(0);
v___x_2211_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
lean_inc_n(v_toPure_2209_, 2);
v___f_2212_ = lean_alloc_closure((void*)(l_Vector_findM_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2212_, 0, v_toPure_2209_);
v___f_2213_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2213_, 0, v___x_2210_);
lean_closure_set(v___f_2213_, 1, v_toPure_2209_);
lean_closure_set(v___f_2213_, 2, v___x_2211_);
v___f_2214_ = lean_alloc_closure((void*)(l_Vector_findSomeM_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2214_, 0, v_f_2205_);
lean_closure_set(v___f_2214_, 1, v_toBind_2208_);
lean_closure_set(v___f_2214_, 2, v___f_2213_);
v_sz_2215_ = lean_array_size(v_as_2206_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2204_, v_as_2206_, v___f_2214_, v_sz_2215_, v___x_2216_, v___x_2211_);
v___x_2218_ = lean_apply_4(v_toBind_2208_, lean_box(0), lean_box(0), v___x_2217_, v___f_2212_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeM_x3f___boxed(lean_object* v_m_2219_, lean_object* v_00_u03b1_2220_, lean_object* v_00_u03b2_2221_, lean_object* v_n_2222_, lean_object* v_inst_2223_, lean_object* v_f_2224_, lean_object* v_as_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Vector_findSomeM_x3f(v_m_2219_, v_00_u03b1_2220_, v_00_u03b2_2221_, v_n_2222_, v_inst_2223_, v_f_2224_, v_as_2225_);
lean_dec(v_n_2222_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0(lean_object* v_toPure_2227_, lean_object* v_a_2228_, uint8_t v_____do__lift_2229_){
_start:
{
if (v_____do__lift_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_a_2228_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_apply_2(v_toPure_2227_, lean_box(0), v___x_2230_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2232_, 0, v_a_2228_);
v___x_2233_ = lean_apply_2(v_toPure_2227_, lean_box(0), v___x_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__0___boxed(lean_object* v_toPure_2234_, lean_object* v_a_2235_, lean_object* v_____do__lift_2236_){
_start:
{
uint8_t v_____do__lift_50__boxed_2237_; lean_object* v_res_2238_; 
v_____do__lift_50__boxed_2237_ = lean_unbox(v_____do__lift_2236_);
v_res_2238_ = l_Vector_findRevM_x3f___redArg___lam__0(v_toPure_2234_, v_a_2235_, v_____do__lift_50__boxed_2237_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg___lam__1(lean_object* v_toPure_2239_, lean_object* v_f_2240_, lean_object* v_toBind_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_inc(v_a_2242_);
v___f_2243_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2243_, 0, v_toPure_2239_);
lean_closure_set(v___f_2243_, 1, v_a_2242_);
v___x_2244_ = lean_apply_1(v_f_2240_, v_a_2242_);
v___x_2245_ = lean_apply_4(v_toBind_2241_, lean_box(0), lean_box(0), v___x_2244_, v___f_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___redArg(lean_object* v_inst_2246_, lean_object* v_f_2247_, lean_object* v_as_2248_){
_start:
{
lean_object* v_toApplicative_2249_; lean_object* v_toBind_2250_; lean_object* v_toPure_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v_toApplicative_2249_ = lean_ctor_get(v_inst_2246_, 0);
v_toBind_2250_ = lean_ctor_get(v_inst_2246_, 1);
v_toPure_2251_ = lean_ctor_get(v_toApplicative_2249_, 1);
lean_inc(v_toBind_2250_);
lean_inc(v_toPure_2251_);
v___f_2252_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2252_, 0, v_toPure_2251_);
lean_closure_set(v___f_2252_, 1, v_f_2247_);
lean_closure_set(v___f_2252_, 2, v_toBind_2250_);
v___x_2253_ = lean_array_get_size(v_as_2248_);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2246_, v___f_2252_, v_as_2248_, v___x_2253_, lean_box(0));
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f(lean_object* v_n_2255_, lean_object* v_00_u03b1_2256_, lean_object* v_m_2257_, lean_object* v_inst_2258_, lean_object* v_f_2259_, lean_object* v_as_2260_){
_start:
{
lean_object* v_toApplicative_2261_; lean_object* v_toBind_2262_; lean_object* v_toPure_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_toApplicative_2261_ = lean_ctor_get(v_inst_2258_, 0);
v_toBind_2262_ = lean_ctor_get(v_inst_2258_, 1);
v_toPure_2263_ = lean_ctor_get(v_toApplicative_2261_, 1);
lean_inc(v_toBind_2262_);
lean_inc(v_toPure_2263_);
v___f_2264_ = lean_alloc_closure((void*)(l_Vector_findRevM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2264_, 0, v_toPure_2263_);
lean_closure_set(v___f_2264_, 1, v_f_2259_);
lean_closure_set(v___f_2264_, 2, v_toBind_2262_);
v___x_2265_ = lean_array_get_size(v_as_2260_);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2258_, v___f_2264_, v_as_2260_, v___x_2265_, lean_box(0));
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRevM_x3f___boxed(lean_object* v_n_2267_, lean_object* v_00_u03b1_2268_, lean_object* v_m_2269_, lean_object* v_inst_2270_, lean_object* v_f_2271_, lean_object* v_as_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Vector_findRevM_x3f(v_n_2267_, v_00_u03b1_2268_, v_m_2269_, v_inst_2270_, v_f_2271_, v_as_2272_);
lean_dec(v_n_2267_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___redArg(lean_object* v_inst_2274_, lean_object* v_f_2275_, lean_object* v_as_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_array_get_size(v_as_2276_);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2274_, v_f_2275_, v_as_2276_, v___x_2277_, lean_box(0));
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f(lean_object* v_m_2279_, lean_object* v_00_u03b1_2280_, lean_object* v_00_u03b2_2281_, lean_object* v_n_2282_, lean_object* v_inst_2283_, lean_object* v_f_2284_, lean_object* v_as_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_array_get_size(v_as_2285_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_2283_, v_f_2284_, v_as_2285_, v___x_2286_, lean_box(0));
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRevM_x3f___boxed(lean_object* v_m_2288_, lean_object* v_00_u03b1_2289_, lean_object* v_00_u03b2_2290_, lean_object* v_n_2291_, lean_object* v_inst_2292_, lean_object* v_f_2293_, lean_object* v_as_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Vector_findSomeRevM_x3f(v_m_2288_, v_00_u03b1_2289_, v_00_u03b2_2290_, v_n_2291_, v_inst_2292_, v_f_2293_, v_as_2294_);
lean_dec(v_n_2291_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0(lean_object* v_f_2296_, lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v_a_2299_, lean_object* v_x_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
lean_inc(v_a_2299_);
v___x_2302_ = lean_apply_1(v_f_2296_, v_a_2299_);
v___x_2303_ = lean_unbox(v___x_2302_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
lean_dec(v_a_2299_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2297_);
return v___x_2304_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec_ref(v___x_2297_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2299_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2298_);
v___x_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg___lam__0___boxed(lean_object* v_f_2309_, lean_object* v___x_2310_, lean_object* v___x_2311_, lean_object* v_a_2312_, lean_object* v_x_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Vector_find_x3f___redArg___lam__0(v_f_2309_, v___x_2310_, v___x_2311_, v_a_2312_, v_x_2313_, v___y_2314_);
lean_dec_ref(v___y_2314_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___redArg(lean_object* v_f_2316_, lean_object* v_as_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___f_2322_; size_t v_sz_2323_; size_t v___x_2324_; lean_object* v___x_2325_; lean_object* v_fst_2326_; 
v___x_2318_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2319_ = lean_box(0);
v___x_2320_ = lean_box(0);
v___x_2321_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2322_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2322_, 0, v_f_2316_);
lean_closure_set(v___f_2322_, 1, v___x_2321_);
lean_closure_set(v___f_2322_, 2, v___x_2320_);
v_sz_2323_ = lean_array_size(v_as_2317_);
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2318_, v_as_2317_, v___f_2322_, v_sz_2323_, v___x_2324_, v___x_2321_);
v_fst_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_fst_2326_);
lean_dec(v___x_2325_);
if (lean_obj_tag(v_fst_2326_) == 0)
{
return v___x_2319_;
}
else
{
lean_object* v_val_2327_; 
v_val_2327_ = lean_ctor_get(v_fst_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v_fst_2326_, 1);
return v_val_2327_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f(lean_object* v_n_2328_, lean_object* v_00_u03b1_2329_, lean_object* v_f_2330_, lean_object* v_as_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; size_t v_sz_2337_; size_t v___x_2338_; lean_object* v___x_2339_; lean_object* v_fst_2340_; 
v___x_2332_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2333_ = lean_box(0);
v___x_2334_ = lean_box(0);
v___x_2335_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2336_ = lean_alloc_closure((void*)(l_Vector_find_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2336_, 0, v_f_2330_);
lean_closure_set(v___f_2336_, 1, v___x_2335_);
lean_closure_set(v___f_2336_, 2, v___x_2334_);
v_sz_2337_ = lean_array_size(v_as_2331_);
v___x_2338_ = ((size_t)0ULL);
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2332_, v_as_2331_, v___f_2336_, v_sz_2337_, v___x_2338_, v___x_2335_);
v_fst_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_fst_2340_);
lean_dec(v___x_2339_);
if (lean_obj_tag(v_fst_2340_) == 0)
{
return v___x_2333_;
}
else
{
lean_object* v_val_2341_; 
v_val_2341_ = lean_ctor_get(v_fst_2340_, 0);
lean_inc(v_val_2341_);
lean_dec_ref_known(v_fst_2340_, 1);
return v_val_2341_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_find_x3f___boxed(lean_object* v_n_2342_, lean_object* v_00_u03b1_2343_, lean_object* v_f_2344_, lean_object* v_as_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Vector_find_x3f(v_n_2342_, v_00_u03b1_2343_, v_f_2344_, v_as_2345_);
lean_dec(v_n_2342_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg___lam__0(lean_object* v_f_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2349_; uint8_t v___x_2350_; 
lean_inc(v_a_2348_);
v___x_2349_ = lean_apply_1(v_f_2347_, v_a_2348_);
v___x_2350_ = lean_unbox(v___x_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec(v_a_2348_);
v___x_2351_ = lean_box(0);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2348_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___redArg(lean_object* v_f_2353_, lean_object* v_as_2354_){
_start:
{
lean_object* v___f_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___f_2355_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2355_, 0, v_f_2353_);
v___x_2356_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2357_ = lean_array_get_size(v_as_2354_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2356_, v___f_2355_, v_as_2354_, v___x_2357_, lean_box(0));
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f(lean_object* v_n_2359_, lean_object* v_00_u03b1_2360_, lean_object* v_f_2361_, lean_object* v_as_2362_){
_start:
{
lean_object* v___f_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___f_2363_ = lean_alloc_closure((void*)(l_Vector_findRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2363_, 0, v_f_2361_);
v___x_2364_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2365_ = lean_array_get_size(v_as_2362_);
v___x_2366_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2364_, v___f_2363_, v_as_2362_, v___x_2365_, lean_box(0));
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Vector_findRev_x3f___boxed(lean_object* v_n_2367_, lean_object* v_00_u03b1_2368_, lean_object* v_f_2369_, lean_object* v_as_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Vector_findRev_x3f(v_n_2367_, v_00_u03b1_2368_, v_f_2369_, v_as_2370_);
lean_dec(v_n_2367_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0(lean_object* v_f_2372_, lean_object* v___x_2373_, lean_object* v___x_2374_, lean_object* v_a_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = lean_apply_1(v_f_2372_, v_a_2375_);
if (lean_obj_tag(v___x_2378_) == 1)
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
lean_dec_ref(v___x_2374_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2373_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
else
{
lean_object* v___x_2382_; 
lean_dec(v___x_2378_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2374_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg___lam__0___boxed(lean_object* v_f_2383_, lean_object* v___x_2384_, lean_object* v___x_2385_, lean_object* v_a_2386_, lean_object* v_x_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Vector_findSome_x3f___redArg___lam__0(v_f_2383_, v___x_2384_, v___x_2385_, v_a_2386_, v_x_2387_, v___y_2388_);
lean_dec_ref(v___y_2388_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___redArg(lean_object* v_f_2390_, lean_object* v_as_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___f_2396_; size_t v_sz_2397_; size_t v___x_2398_; lean_object* v___x_2399_; lean_object* v_fst_2400_; 
v___x_2392_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2393_ = lean_box(0);
v___x_2394_ = lean_box(0);
v___x_2395_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2396_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2396_, 0, v_f_2390_);
lean_closure_set(v___f_2396_, 1, v___x_2394_);
lean_closure_set(v___f_2396_, 2, v___x_2395_);
v_sz_2397_ = lean_array_size(v_as_2391_);
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2392_, v_as_2391_, v___f_2396_, v_sz_2397_, v___x_2398_, v___x_2395_);
v_fst_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_fst_2400_);
lean_dec(v___x_2399_);
if (lean_obj_tag(v_fst_2400_) == 0)
{
return v___x_2393_;
}
else
{
lean_object* v_val_2401_; 
v_val_2401_ = lean_ctor_get(v_fst_2400_, 0);
lean_inc(v_val_2401_);
lean_dec_ref_known(v_fst_2400_, 1);
return v_val_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_n_2404_, lean_object* v_f_2405_, lean_object* v_as_2406_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___f_2411_; size_t v_sz_2412_; size_t v___x_2413_; lean_object* v___x_2414_; lean_object* v_fst_2415_; 
v___x_2407_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2408_ = lean_box(0);
v___x_2409_ = lean_box(0);
v___x_2410_ = ((lean_object*)(l_Vector_findM_x3f___redArg___closed__0));
v___f_2411_ = lean_alloc_closure((void*)(l_Vector_findSome_x3f___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2411_, 0, v_f_2405_);
lean_closure_set(v___f_2411_, 1, v___x_2409_);
lean_closure_set(v___f_2411_, 2, v___x_2410_);
v_sz_2412_ = lean_array_size(v_as_2406_);
v___x_2413_ = ((size_t)0ULL);
v___x_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2407_, v_as_2406_, v___f_2411_, v_sz_2412_, v___x_2413_, v___x_2410_);
v_fst_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_fst_2415_);
lean_dec(v___x_2414_);
if (lean_obj_tag(v_fst_2415_) == 0)
{
return v___x_2408_;
}
else
{
lean_object* v_val_2416_; 
v_val_2416_ = lean_ctor_get(v_fst_2415_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v_fst_2415_, 1);
return v_val_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_findSome_x3f___boxed(lean_object* v_00_u03b1_2417_, lean_object* v_00_u03b2_2418_, lean_object* v_n_2419_, lean_object* v_f_2420_, lean_object* v_as_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Vector_findSome_x3f(v_00_u03b1_2417_, v_00_u03b2_2418_, v_n_2419_, v_f_2420_, v_as_2421_);
lean_dec(v_n_2419_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg___lam__0(lean_object* v_f_2423_, lean_object* v_x_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_apply_1(v_f_2423_, v_x_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___redArg(lean_object* v_f_2426_, lean_object* v_as_2427_){
_start:
{
lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___f_2428_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2428_, 0, v_f_2426_);
v___x_2429_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2430_ = lean_array_get_size(v_as_2427_);
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2429_, v___f_2428_, v_as_2427_, v___x_2430_, lean_box(0));
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f(lean_object* v_00_u03b1_2432_, lean_object* v_00_u03b2_2433_, lean_object* v_n_2434_, lean_object* v_f_2435_, lean_object* v_as_2436_){
_start:
{
lean_object* v___f_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___f_2437_ = lean_alloc_closure((void*)(l_Vector_findSomeRev_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2437_, 0, v_f_2435_);
v___x_2438_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2439_ = lean_array_get_size(v_as_2436_);
v___x_2440_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v___x_2438_, v___f_2437_, v_as_2436_, v___x_2439_, lean_box(0));
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Vector_findSomeRev_x3f___boxed(lean_object* v_00_u03b1_2441_, lean_object* v_00_u03b2_2442_, lean_object* v_n_2443_, lean_object* v_f_2444_, lean_object* v_as_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Vector_findSomeRev_x3f(v_00_u03b1_2441_, v_00_u03b2_2442_, v_n_2443_, v_f_2444_, v_as_2445_);
lean_dec(v_n_2443_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf___redArg(lean_object* v_inst_2447_, lean_object* v_xs_2448_, lean_object* v_ys_2449_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = l_Array_isPrefixOf___redArg(v_inst_2447_, v_xs_2448_, v_ys_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___redArg___boxed(lean_object* v_inst_2451_, lean_object* v_xs_2452_, lean_object* v_ys_2453_){
_start:
{
uint8_t v_res_2454_; lean_object* v_r_2455_; 
v_res_2454_ = l_Vector_isPrefixOf___redArg(v_inst_2451_, v_xs_2452_, v_ys_2453_);
lean_dec_ref(v_ys_2453_);
lean_dec_ref(v_xs_2452_);
v_r_2455_ = lean_box(v_res_2454_);
return v_r_2455_;
}
}
LEAN_EXPORT uint8_t l_Vector_isPrefixOf(lean_object* v_00_u03b1_2456_, lean_object* v_m_2457_, lean_object* v_n_2458_, lean_object* v_inst_2459_, lean_object* v_xs_2460_, lean_object* v_ys_2461_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = l_Array_isPrefixOf___redArg(v_inst_2459_, v_xs_2460_, v_ys_2461_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Vector_isPrefixOf___boxed(lean_object* v_00_u03b1_2463_, lean_object* v_m_2464_, lean_object* v_n_2465_, lean_object* v_inst_2466_, lean_object* v_xs_2467_, lean_object* v_ys_2468_){
_start:
{
uint8_t v_res_2469_; lean_object* v_r_2470_; 
v_res_2469_ = l_Vector_isPrefixOf(v_00_u03b1_2463_, v_m_2464_, v_n_2465_, v_inst_2466_, v_xs_2467_, v_ys_2468_);
lean_dec_ref(v_ys_2468_);
lean_dec_ref(v_xs_2467_);
lean_dec(v_n_2465_);
lean_dec(v_m_2464_);
v_r_2470_ = lean_box(v_res_2469_);
return v_r_2470_;
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___redArg(lean_object* v_inst_2471_, lean_object* v_p_2472_, lean_object* v_xs_2473_){
_start:
{
lean_object* v_toApplicative_2474_; lean_object* v_toPure_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; uint8_t v___x_2478_; 
v_toApplicative_2474_ = lean_ctor_get(v_inst_2471_, 0);
v_toPure_2475_ = lean_ctor_get(v_toApplicative_2474_, 1);
v___x_2476_ = lean_unsigned_to_nat(0u);
v___x_2477_ = lean_array_get_size(v_xs_2473_);
v___x_2478_ = lean_nat_dec_lt(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_inc(v_toPure_2475_);
lean_dec_ref(v_xs_2473_);
lean_dec(v_p_2472_);
lean_dec_ref(v_inst_2471_);
v___x_2479_ = lean_box(v___x_2478_);
v___x_2480_ = lean_apply_2(v_toPure_2475_, lean_box(0), v___x_2479_);
return v___x_2480_;
}
else
{
if (v___x_2478_ == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_inc(v_toPure_2475_);
lean_dec_ref(v_xs_2473_);
lean_dec(v_p_2472_);
lean_dec_ref(v_inst_2471_);
v___x_2481_ = lean_box(v___x_2478_);
v___x_2482_ = lean_apply_2(v_toPure_2475_, lean_box(0), v___x_2481_);
return v___x_2482_;
}
else
{
size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = ((size_t)0ULL);
v___x_2484_ = lean_usize_of_nat(v___x_2477_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2471_, v_p_2472_, v_xs_2473_, v___x_2483_, v___x_2484_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM(lean_object* v_m_2486_, lean_object* v_00_u03b1_2487_, lean_object* v_n_2488_, lean_object* v_inst_2489_, lean_object* v_p_2490_, lean_object* v_xs_2491_){
_start:
{
lean_object* v_toApplicative_2492_; lean_object* v_toPure_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v_toApplicative_2492_ = lean_ctor_get(v_inst_2489_, 0);
v_toPure_2493_ = lean_ctor_get(v_toApplicative_2492_, 1);
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_array_get_size(v_xs_2491_);
v___x_2496_ = lean_nat_dec_lt(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_inc(v_toPure_2493_);
lean_dec_ref(v_xs_2491_);
lean_dec(v_p_2490_);
lean_dec_ref(v_inst_2489_);
v___x_2497_ = lean_box(v___x_2496_);
v___x_2498_ = lean_apply_2(v_toPure_2493_, lean_box(0), v___x_2497_);
return v___x_2498_;
}
else
{
if (v___x_2496_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_inc(v_toPure_2493_);
lean_dec_ref(v_xs_2491_);
lean_dec(v_p_2490_);
lean_dec_ref(v_inst_2489_);
v___x_2499_ = lean_box(v___x_2496_);
v___x_2500_ = lean_apply_2(v_toPure_2493_, lean_box(0), v___x_2499_);
return v___x_2500_;
}
else
{
size_t v___x_2501_; size_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = ((size_t)0ULL);
v___x_2502_ = lean_usize_of_nat(v___x_2495_);
v___x_2503_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2489_, v_p_2490_, v_xs_2491_, v___x_2501_, v___x_2502_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_anyM___boxed(lean_object* v_m_2504_, lean_object* v_00_u03b1_2505_, lean_object* v_n_2506_, lean_object* v_inst_2507_, lean_object* v_p_2508_, lean_object* v_xs_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Vector_anyM(v_m_2504_, v_00_u03b1_2505_, v_n_2506_, v_inst_2507_, v_p_2508_, v_xs_2509_);
lean_dec(v_n_2506_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0(lean_object* v_toPure_2511_, uint8_t v_____do__lift_2512_){
_start:
{
if (v_____do__lift_2512_ == 0)
{
uint8_t v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = 1;
v___x_2514_ = lean_box(v___x_2513_);
v___x_2515_ = lean_apply_2(v_toPure_2511_, lean_box(0), v___x_2514_);
return v___x_2515_;
}
else
{
uint8_t v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = 0;
v___x_2517_ = lean_box(v___x_2516_);
v___x_2518_ = lean_apply_2(v_toPure_2511_, lean_box(0), v___x_2517_);
return v___x_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__0___boxed(lean_object* v_toPure_2519_, lean_object* v_____do__lift_2520_){
_start:
{
uint8_t v_____do__lift_112__boxed_2521_; lean_object* v_res_2522_; 
v_____do__lift_112__boxed_2521_ = lean_unbox(v_____do__lift_2520_);
v_res_2522_ = l_Vector_allM___redArg___lam__0(v_toPure_2519_, v_____do__lift_112__boxed_2521_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1(lean_object* v_toPure_2523_, uint8_t v___x_2524_, uint8_t v_____do__lift_2525_){
_start:
{
if (v_____do__lift_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2526_ = lean_box(v___x_2524_);
v___x_2527_ = lean_apply_2(v_toPure_2523_, lean_box(0), v___x_2526_);
return v___x_2527_;
}
else
{
uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = 0;
v___x_2529_ = lean_box(v___x_2528_);
v___x_2530_ = lean_apply_2(v_toPure_2523_, lean_box(0), v___x_2529_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__1___boxed(lean_object* v_toPure_2531_, lean_object* v___x_2532_, lean_object* v_____do__lift_2533_){
_start:
{
uint8_t v___x_127__boxed_2534_; uint8_t v_____do__lift_128__boxed_2535_; lean_object* v_res_2536_; 
v___x_127__boxed_2534_ = lean_unbox(v___x_2532_);
v_____do__lift_128__boxed_2535_ = lean_unbox(v_____do__lift_2533_);
v_res_2536_ = l_Vector_allM___redArg___lam__1(v_toPure_2531_, v___x_127__boxed_2534_, v_____do__lift_128__boxed_2535_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg___lam__2(lean_object* v_p_2537_, lean_object* v_toBind_2538_, lean_object* v___f_2539_, lean_object* v_v_2540_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_apply_1(v_p_2537_, v_v_2540_);
v___x_2542_ = lean_apply_4(v_toBind_2538_, lean_box(0), lean_box(0), v___x_2541_, v___f_2539_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Vector_allM___redArg(lean_object* v_inst_2543_, lean_object* v_p_2544_, lean_object* v_xs_2545_){
_start:
{
lean_object* v_toApplicative_2546_; lean_object* v_toBind_2547_; lean_object* v_toPure_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___f_2551_; uint8_t v___x_2552_; 
v_toApplicative_2546_ = lean_ctor_get(v_inst_2543_, 0);
v_toBind_2547_ = lean_ctor_get(v_inst_2543_, 1);
lean_inc(v_toBind_2547_);
v_toPure_2548_ = lean_ctor_get(v_toApplicative_2546_, 1);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_array_get_size(v_xs_2545_);
lean_inc(v_toPure_2548_);
v___f_2551_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2551_, 0, v_toPure_2548_);
v___x_2552_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_inc(v_toPure_2548_);
lean_dec_ref(v_xs_2545_);
lean_dec(v_p_2544_);
lean_dec_ref(v_inst_2543_);
v___x_2553_ = lean_box(v___x_2552_);
v___x_2554_ = lean_apply_2(v_toPure_2548_, lean_box(0), v___x_2553_);
v___x_2555_ = lean_apply_4(v_toBind_2547_, lean_box(0), lean_box(0), v___x_2554_, v___f_2551_);
return v___x_2555_;
}
else
{
if (v___x_2552_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_inc(v_toPure_2548_);
lean_dec_ref(v_xs_2545_);
lean_dec(v_p_2544_);
lean_dec_ref(v_inst_2543_);
v___x_2556_ = lean_box(v___x_2552_);
v___x_2557_ = lean_apply_2(v_toPure_2548_, lean_box(0), v___x_2556_);
v___x_2558_ = lean_apply_4(v_toBind_2547_, lean_box(0), lean_box(0), v___x_2557_, v___f_2551_);
return v___x_2558_;
}
else
{
lean_object* v___x_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; size_t v___x_2562_; size_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2559_ = lean_box(v___x_2552_);
lean_inc(v_toPure_2548_);
v___f_2560_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2560_, 0, v_toPure_2548_);
lean_closure_set(v___f_2560_, 1, v___x_2559_);
lean_inc(v_toBind_2547_);
v___f_2561_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2561_, 0, v_p_2544_);
lean_closure_set(v___f_2561_, 1, v_toBind_2547_);
lean_closure_set(v___f_2561_, 2, v___f_2560_);
v___x_2562_ = ((size_t)0ULL);
v___x_2563_ = lean_usize_of_nat(v___x_2550_);
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2543_, v___f_2561_, v_xs_2545_, v___x_2562_, v___x_2563_);
v___x_2565_ = lean_apply_4(v_toBind_2547_, lean_box(0), lean_box(0), v___x_2564_, v___f_2551_);
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM(lean_object* v_m_2566_, lean_object* v_00_u03b1_2567_, lean_object* v_n_2568_, lean_object* v_inst_2569_, lean_object* v_p_2570_, lean_object* v_xs_2571_){
_start:
{
lean_object* v_toApplicative_2572_; lean_object* v_toBind_2573_; lean_object* v_toPure_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; uint8_t v___x_2578_; 
v_toApplicative_2572_ = lean_ctor_get(v_inst_2569_, 0);
v_toBind_2573_ = lean_ctor_get(v_inst_2569_, 1);
lean_inc(v_toBind_2573_);
v_toPure_2574_ = lean_ctor_get(v_toApplicative_2572_, 1);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_array_get_size(v_xs_2571_);
lean_inc(v_toPure_2574_);
v___f_2577_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2577_, 0, v_toPure_2574_);
v___x_2578_ = lean_nat_dec_lt(v___x_2575_, v___x_2576_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_inc(v_toPure_2574_);
lean_dec_ref(v_xs_2571_);
lean_dec(v_p_2570_);
lean_dec_ref(v_inst_2569_);
v___x_2579_ = lean_box(v___x_2578_);
v___x_2580_ = lean_apply_2(v_toPure_2574_, lean_box(0), v___x_2579_);
v___x_2581_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2580_, v___f_2577_);
return v___x_2581_;
}
else
{
if (v___x_2578_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
lean_inc(v_toPure_2574_);
lean_dec_ref(v_xs_2571_);
lean_dec(v_p_2570_);
lean_dec_ref(v_inst_2569_);
v___x_2582_ = lean_box(v___x_2578_);
v___x_2583_ = lean_apply_2(v_toPure_2574_, lean_box(0), v___x_2582_);
v___x_2584_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2583_, v___f_2577_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; size_t v___x_2588_; size_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2585_ = lean_box(v___x_2578_);
lean_inc(v_toPure_2574_);
v___f_2586_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_2586_, 0, v_toPure_2574_);
lean_closure_set(v___f_2586_, 1, v___x_2585_);
lean_inc(v_toBind_2573_);
v___f_2587_ = lean_alloc_closure((void*)(l_Vector_allM___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2587_, 0, v_p_2570_);
lean_closure_set(v___f_2587_, 1, v_toBind_2573_);
lean_closure_set(v___f_2587_, 2, v___f_2586_);
v___x_2588_ = ((size_t)0ULL);
v___x_2589_ = lean_usize_of_nat(v___x_2576_);
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2569_, v___f_2587_, v_xs_2571_, v___x_2588_, v___x_2589_);
v___x_2591_ = lean_apply_4(v_toBind_2573_, lean_box(0), lean_box(0), v___x_2590_, v___f_2577_);
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_allM___boxed(lean_object* v_m_2592_, lean_object* v_00_u03b1_2593_, lean_object* v_n_2594_, lean_object* v_inst_2595_, lean_object* v_p_2596_, lean_object* v_xs_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Vector_allM(v_m_2592_, v_00_u03b1_2593_, v_n_2594_, v_inst_2595_, v_p_2596_, v_xs_2597_);
lean_dec(v_n_2594_);
return v_res_2598_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg___lam__0(lean_object* v_p_2599_, lean_object* v_x_2600_){
_start:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = lean_apply_1(v_p_2599_, v_x_2600_);
v___x_2602_ = lean_unbox(v___x_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___lam__0___boxed(lean_object* v_p_2603_, lean_object* v_x_2604_){
_start:
{
uint8_t v_res_2605_; lean_object* v_r_2606_; 
v_res_2605_ = l_Vector_any___redArg___lam__0(v_p_2603_, v_x_2604_);
v_r_2606_ = lean_box(v_res_2605_);
return v_r_2606_;
}
}
LEAN_EXPORT uint8_t l_Vector_any___redArg(lean_object* v_xs_2607_, lean_object* v_p_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_array_get_size(v_xs_2607_);
v___x_2611_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2612_ = lean_nat_dec_lt(v___x_2609_, v___x_2610_);
if (v___x_2612_ == 0)
{
lean_dec_ref(v_p_2608_);
lean_dec_ref(v_xs_2607_);
return v___x_2612_;
}
else
{
if (v___x_2612_ == 0)
{
lean_dec_ref(v_p_2608_);
lean_dec_ref(v_xs_2607_);
return v___x_2612_;
}
else
{
lean_object* v___f_2613_; size_t v___x_2614_; size_t v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___f_2613_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2613_, 0, v_p_2608_);
v___x_2614_ = ((size_t)0ULL);
v___x_2615_ = lean_usize_of_nat(v___x_2610_);
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2611_, v___f_2613_, v_xs_2607_, v___x_2614_, v___x_2615_);
v___x_2617_ = lean_unbox(v___x_2616_);
lean_dec(v___x_2616_);
return v___x_2617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___redArg___boxed(lean_object* v_xs_2618_, lean_object* v_p_2619_){
_start:
{
uint8_t v_res_2620_; lean_object* v_r_2621_; 
v_res_2620_ = l_Vector_any___redArg(v_xs_2618_, v_p_2619_);
v_r_2621_ = lean_box(v_res_2620_);
return v_r_2621_;
}
}
LEAN_EXPORT uint8_t l_Vector_any(lean_object* v_00_u03b1_2622_, lean_object* v_n_2623_, lean_object* v_xs_2624_, lean_object* v_p_2625_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2626_ = lean_unsigned_to_nat(0u);
v___x_2627_ = lean_array_get_size(v_xs_2624_);
v___x_2628_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2629_ = lean_nat_dec_lt(v___x_2626_, v___x_2627_);
if (v___x_2629_ == 0)
{
lean_dec_ref(v_p_2625_);
lean_dec_ref(v_xs_2624_);
return v___x_2629_;
}
else
{
if (v___x_2629_ == 0)
{
lean_dec_ref(v_p_2625_);
lean_dec_ref(v_xs_2624_);
return v___x_2629_;
}
else
{
lean_object* v___f_2630_; size_t v___x_2631_; size_t v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___f_2630_ = lean_alloc_closure((void*)(l_Vector_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2630_, 0, v_p_2625_);
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = lean_usize_of_nat(v___x_2627_);
v___x_2633_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2628_, v___f_2630_, v_xs_2624_, v___x_2631_, v___x_2632_);
v___x_2634_ = lean_unbox(v___x_2633_);
lean_dec(v___x_2633_);
return v___x_2634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_any___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_n_2636_, lean_object* v_xs_2637_, lean_object* v_p_2638_){
_start:
{
uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_res_2639_ = l_Vector_any(v_00_u03b1_2635_, v_n_2636_, v_xs_2637_, v_p_2638_);
lean_dec(v_n_2636_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg___lam__0(lean_object* v_p_2641_, uint8_t v___x_2642_, lean_object* v_v_2643_){
_start:
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_apply_1(v_p_2641_, v_v_2643_);
v___x_2645_ = lean_unbox(v___x_2644_);
if (v___x_2645_ == 0)
{
return v___x_2642_;
}
else
{
uint8_t v___x_2646_; 
v___x_2646_ = 0;
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___lam__0___boxed(lean_object* v_p_2647_, lean_object* v___x_2648_, lean_object* v_v_2649_){
_start:
{
uint8_t v___x_75__boxed_2650_; uint8_t v_res_2651_; lean_object* v_r_2652_; 
v___x_75__boxed_2650_ = lean_unbox(v___x_2648_);
v_res_2651_ = l_Vector_all___redArg___lam__0(v_p_2647_, v___x_75__boxed_2650_, v_v_2649_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT uint8_t l_Vector_all___redArg(lean_object* v_xs_2653_, lean_object* v_p_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_array_get_size(v_xs_2653_);
v___x_2657_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2658_ = lean_nat_dec_lt(v___x_2655_, v___x_2656_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
lean_dec_ref(v_p_2654_);
lean_dec_ref(v_xs_2653_);
v___x_2659_ = 1;
return v___x_2659_;
}
else
{
if (v___x_2658_ == 0)
{
lean_dec_ref(v_p_2654_);
lean_dec_ref(v_xs_2653_);
return v___x_2658_;
}
else
{
lean_object* v___x_2660_; lean_object* v___f_2661_; size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2660_ = lean_box(v___x_2658_);
v___f_2661_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2661_, 0, v_p_2654_);
lean_closure_set(v___f_2661_, 1, v___x_2660_);
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2656_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2657_, v___f_2661_, v_xs_2653_, v___x_2662_, v___x_2663_);
v___x_2665_ = lean_unbox(v___x_2664_);
lean_dec(v___x_2664_);
if (v___x_2665_ == 0)
{
return v___x_2658_;
}
else
{
uint8_t v___x_2666_; 
v___x_2666_ = 0;
return v___x_2666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___redArg___boxed(lean_object* v_xs_2667_, lean_object* v_p_2668_){
_start:
{
uint8_t v_res_2669_; lean_object* v_r_2670_; 
v_res_2669_ = l_Vector_all___redArg(v_xs_2667_, v_p_2668_);
v_r_2670_ = lean_box(v_res_2669_);
return v_r_2670_;
}
}
LEAN_EXPORT uint8_t l_Vector_all(lean_object* v_00_u03b1_2671_, lean_object* v_n_2672_, lean_object* v_xs_2673_, lean_object* v_p_2674_){
_start:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_array_get_size(v_xs_2673_);
v___x_2677_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2678_ = lean_nat_dec_lt(v___x_2675_, v___x_2676_);
if (v___x_2678_ == 0)
{
uint8_t v___x_2679_; 
lean_dec_ref(v_p_2674_);
lean_dec_ref(v_xs_2673_);
v___x_2679_ = 1;
return v___x_2679_;
}
else
{
if (v___x_2678_ == 0)
{
lean_dec_ref(v_p_2674_);
lean_dec_ref(v_xs_2673_);
return v___x_2678_;
}
else
{
lean_object* v___x_2680_; lean_object* v___f_2681_; size_t v___x_2682_; size_t v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2680_ = lean_box(v___x_2678_);
v___f_2681_ = lean_alloc_closure((void*)(l_Vector_all___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2681_, 0, v_p_2674_);
lean_closure_set(v___f_2681_, 1, v___x_2680_);
v___x_2682_ = ((size_t)0ULL);
v___x_2683_ = lean_usize_of_nat(v___x_2676_);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v___x_2677_, v___f_2681_, v_xs_2673_, v___x_2682_, v___x_2683_);
v___x_2685_ = lean_unbox(v___x_2684_);
lean_dec(v___x_2684_);
if (v___x_2685_ == 0)
{
return v___x_2678_;
}
else
{
uint8_t v___x_2686_; 
v___x_2686_ = 0;
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_all___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_n_2688_, lean_object* v_xs_2689_, lean_object* v_p_2690_){
_start:
{
uint8_t v_res_2691_; lean_object* v_r_2692_; 
v_res_2691_ = l_Vector_all(v_00_u03b1_2687_, v_n_2688_, v_xs_2689_, v_p_2690_);
lean_dec(v_n_2688_);
v_r_2692_ = lean_box(v_res_2691_);
return v_r_2692_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0(lean_object* v_p_2693_, lean_object* v_x1_2694_, lean_object* v_x2_2695_){
_start:
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = lean_apply_1(v_p_2693_, v_x1_2694_);
v___x_2697_ = lean_unbox(v___x_2696_);
if (v___x_2697_ == 0)
{
lean_inc(v_x2_2695_);
return v_x2_2695_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_unsigned_to_nat(1u);
v___x_2699_ = lean_nat_add(v_x2_2695_, v___x_2698_);
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg___lam__0___boxed(lean_object* v_p_2700_, lean_object* v_x1_2701_, lean_object* v_x2_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Vector_countP___redArg___lam__0(v_p_2700_, v_x1_2701_, v_x2_2702_);
lean_dec(v_x2_2702_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Vector_countP___redArg(lean_object* v_p_2704_, lean_object* v_xs_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = lean_array_get_size(v_xs_2705_);
v___x_2708_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2709_ = lean_nat_dec_lt(v___x_2706_, v___x_2707_);
if (v___x_2709_ == 0)
{
lean_dec_ref(v_xs_2705_);
lean_dec_ref(v_p_2704_);
return v___x_2706_;
}
else
{
lean_object* v___f_2710_; size_t v___x_2711_; size_t v___x_2712_; lean_object* v___x_2713_; 
v___f_2710_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2710_, 0, v_p_2704_);
v___x_2711_ = lean_usize_of_nat(v___x_2707_);
v___x_2712_ = ((size_t)0ULL);
v___x_2713_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2708_, v___f_2710_, v_xs_2705_, v___x_2711_, v___x_2712_, v___x_2706_);
return v___x_2713_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP(lean_object* v_00_u03b1_2714_, lean_object* v_n_2715_, lean_object* v_p_2716_, lean_object* v_xs_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2718_ = lean_unsigned_to_nat(0u);
v___x_2719_ = lean_array_get_size(v_xs_2717_);
v___x_2720_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2721_ = lean_nat_dec_lt(v___x_2718_, v___x_2719_);
if (v___x_2721_ == 0)
{
lean_dec_ref(v_xs_2717_);
lean_dec_ref(v_p_2716_);
return v___x_2718_;
}
else
{
lean_object* v___f_2722_; size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
v___f_2722_ = lean_alloc_closure((void*)(l_Vector_countP___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2722_, 0, v_p_2716_);
v___x_2723_ = lean_usize_of_nat(v___x_2719_);
v___x_2724_ = ((size_t)0ULL);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2720_, v___f_2722_, v_xs_2717_, v___x_2723_, v___x_2724_, v___x_2718_);
return v___x_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_countP___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_n_2727_, lean_object* v_p_2728_, lean_object* v_xs_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Vector_countP(v_00_u03b1_2726_, v_n_2727_, v_p_2728_, v_xs_2729_);
lean_dec(v_n_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0(lean_object* v_inst_2731_, lean_object* v_a_2732_, lean_object* v_x1_2733_, lean_object* v_x2_2734_){
_start:
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = lean_apply_2(v_inst_2731_, v_x1_2733_, v_a_2732_);
v___x_2736_ = lean_unbox(v___x_2735_);
if (v___x_2736_ == 0)
{
lean_inc(v_x2_2734_);
return v_x2_2734_;
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_unsigned_to_nat(1u);
v___x_2738_ = lean_nat_add(v_x2_2734_, v___x_2737_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg___lam__0___boxed(lean_object* v_inst_2739_, lean_object* v_a_2740_, lean_object* v_x1_2741_, lean_object* v_x2_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Vector_count___redArg___lam__0(v_inst_2739_, v_a_2740_, v_x1_2741_, v_x2_2742_);
lean_dec(v_x2_2742_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Vector_count___redArg(lean_object* v_inst_2744_, lean_object* v_a_2745_, lean_object* v_xs_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = lean_array_get_size(v_xs_2746_);
v___x_2749_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2750_ = lean_nat_dec_lt(v___x_2747_, v___x_2748_);
if (v___x_2750_ == 0)
{
lean_dec_ref(v_xs_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_inst_2744_);
return v___x_2747_;
}
else
{
lean_object* v___f_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v___f_2751_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2751_, 0, v_inst_2744_);
lean_closure_set(v___f_2751_, 1, v_a_2745_);
v___x_2752_ = lean_usize_of_nat(v___x_2748_);
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2749_, v___f_2751_, v_xs_2746_, v___x_2752_, v___x_2753_, v___x_2747_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count(lean_object* v_00_u03b1_2755_, lean_object* v_n_2756_, lean_object* v_inst_2757_, lean_object* v_a_2758_, lean_object* v_xs_2759_){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2760_ = lean_unsigned_to_nat(0u);
v___x_2761_ = lean_array_get_size(v_xs_2759_);
v___x_2762_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2763_ = lean_nat_dec_lt(v___x_2760_, v___x_2761_);
if (v___x_2763_ == 0)
{
lean_dec_ref(v_xs_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_inst_2757_);
return v___x_2760_;
}
else
{
lean_object* v___f_2764_; size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
v___f_2764_ = lean_alloc_closure((void*)(l_Vector_count___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2764_, 0, v_inst_2757_);
lean_closure_set(v___f_2764_, 1, v_a_2758_);
v___x_2765_ = lean_usize_of_nat(v___x_2761_);
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2762_, v___f_2764_, v_xs_2759_, v___x_2765_, v___x_2766_, v___x_2760_);
return v___x_2767_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_count___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_n_2769_, lean_object* v_inst_2770_, lean_object* v_a_2771_, lean_object* v_xs_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Vector_count(v_00_u03b1_2768_, v_n_2769_, v_inst_2770_, v_a_2771_, v_xs_2772_);
lean_dec(v_n_2769_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___redArg(lean_object* v_inst_2774_, lean_object* v_xs_2775_, lean_object* v_a_2776_, lean_object* v_b_2777_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Array_replace___redArg(v_inst_2774_, v_xs_2775_, v_a_2776_, v_b_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace(lean_object* v_00_u03b1_2779_, lean_object* v_n_2780_, lean_object* v_inst_2781_, lean_object* v_xs_2782_, lean_object* v_a_2783_, lean_object* v_b_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Array_replace___redArg(v_inst_2781_, v_xs_2782_, v_a_2783_, v_b_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Vector_replace___boxed(lean_object* v_00_u03b1_2786_, lean_object* v_n_2787_, lean_object* v_inst_2788_, lean_object* v_xs_2789_, lean_object* v_a_2790_, lean_object* v_b_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_Vector_replace(v_00_u03b1_2786_, v_n_2787_, v_inst_2788_, v_xs_2789_, v_a_2790_, v_b_2791_);
lean_dec(v_n_2787_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg___lam__0(lean_object* v_inst_2793_, lean_object* v_x1_2794_, lean_object* v_x2_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_apply_2(v_inst_2793_, v_x1_2794_, v_x2_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Vector_sum___redArg(lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_xs_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2800_ = lean_array_get_size(v_xs_2799_);
v___x_2801_ = lean_unsigned_to_nat(0u);
v___x_2802_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2803_ = lean_nat_dec_lt(v___x_2801_, v___x_2800_);
if (v___x_2803_ == 0)
{
lean_dec_ref(v_xs_2799_);
lean_dec(v_inst_2797_);
return v_inst_2798_;
}
else
{
lean_object* v___f_2804_; size_t v___x_2805_; size_t v___x_2806_; lean_object* v___x_2807_; 
v___f_2804_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2804_, 0, v_inst_2797_);
v___x_2805_ = lean_usize_of_nat(v___x_2800_);
v___x_2806_ = ((size_t)0ULL);
v___x_2807_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2802_, v___f_2804_, v_xs_2799_, v___x_2805_, v___x_2806_, v_inst_2798_);
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum(lean_object* v_00_u03b1_2808_, lean_object* v_n_2809_, lean_object* v_inst_2810_, lean_object* v_inst_2811_, lean_object* v_xs_2812_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2813_ = lean_array_get_size(v_xs_2812_);
v___x_2814_ = lean_unsigned_to_nat(0u);
v___x_2815_ = ((lean_object*)(l_Vector_foldl___redArg___closed__9));
v___x_2816_ = lean_nat_dec_lt(v___x_2814_, v___x_2813_);
if (v___x_2816_ == 0)
{
lean_dec_ref(v_xs_2812_);
lean_dec(v_inst_2810_);
return v_inst_2811_;
}
else
{
lean_object* v___f_2817_; size_t v___x_2818_; size_t v___x_2819_; lean_object* v___x_2820_; 
v___f_2817_ = lean_alloc_closure((void*)(l_Vector_sum___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2817_, 0, v_inst_2810_);
v___x_2818_ = lean_usize_of_nat(v___x_2813_);
v___x_2819_ = ((size_t)0ULL);
v___x_2820_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2815_, v___f_2817_, v_xs_2812_, v___x_2818_, v___x_2819_, v_inst_2811_);
return v___x_2820_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_sum___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_n_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_, lean_object* v_xs_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Vector_sum(v_00_u03b1_2821_, v_n_2822_, v_inst_2823_, v_inst_2824_, v_xs_2825_);
lean_dec(v_n_2822_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Vector_prod___redArg(lean_object* v_inst_2827_, lean_object* v_inst_2828_, lean_object* v_xs_2829_){
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
LEAN_EXPORT lean_object* l_Vector_prod(lean_object* v_00_u03b1_2838_, lean_object* v_n_2839_, lean_object* v_inst_2840_, lean_object* v_inst_2841_, lean_object* v_xs_2842_){
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
LEAN_EXPORT lean_object* l_Vector_prod___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_n_2852_, lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_xs_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Vector_prod(v_00_u03b1_2851_, v_n_2852_, v_inst_2853_, v_inst_2854_, v_xs_2855_);
lean_dec(v_n_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg(lean_object* v_m_2857_, lean_object* v_n_2858_, lean_object* v_a_2859_, lean_object* v_xs_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_nat_sub(v_n_2858_, v_m_2857_);
v___x_2862_ = lean_mk_array(v___x_2861_, v_a_2859_);
v___x_2863_ = l_Array_append___redArg(v___x_2862_, v_xs_2860_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___redArg___boxed(lean_object* v_m_2864_, lean_object* v_n_2865_, lean_object* v_a_2866_, lean_object* v_xs_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Vector_leftpad___redArg(v_m_2864_, v_n_2865_, v_a_2866_, v_xs_2867_);
lean_dec_ref(v_xs_2867_);
lean_dec(v_n_2865_);
lean_dec(v_m_2864_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad(lean_object* v_00_u03b1_2869_, lean_object* v_m_2870_, lean_object* v_n_2871_, lean_object* v_a_2872_, lean_object* v_xs_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_nat_sub(v_n_2871_, v_m_2870_);
v___x_2875_ = lean_mk_array(v___x_2874_, v_a_2872_);
v___x_2876_ = l_Array_append___redArg(v___x_2875_, v_xs_2873_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Vector_leftpad___boxed(lean_object* v_00_u03b1_2877_, lean_object* v_m_2878_, lean_object* v_n_2879_, lean_object* v_a_2880_, lean_object* v_xs_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Vector_leftpad(v_00_u03b1_2877_, v_m_2878_, v_n_2879_, v_a_2880_, v_xs_2881_);
lean_dec_ref(v_xs_2881_);
lean_dec(v_n_2879_);
lean_dec(v_m_2878_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg(lean_object* v_m_2883_, lean_object* v_n_2884_, lean_object* v_a_2885_, lean_object* v_xs_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2887_ = lean_nat_sub(v_n_2884_, v_m_2883_);
v___x_2888_ = lean_mk_array(v___x_2887_, v_a_2885_);
v___x_2889_ = l_Array_append___redArg(v_xs_2886_, v___x_2888_);
lean_dec_ref(v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___redArg___boxed(lean_object* v_m_2890_, lean_object* v_n_2891_, lean_object* v_a_2892_, lean_object* v_xs_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Vector_rightpad___redArg(v_m_2890_, v_n_2891_, v_a_2892_, v_xs_2893_);
lean_dec(v_n_2891_);
lean_dec(v_m_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad(lean_object* v_00_u03b1_2895_, lean_object* v_m_2896_, lean_object* v_n_2897_, lean_object* v_a_2898_, lean_object* v_xs_2899_){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_nat_sub(v_n_2897_, v_m_2896_);
v___x_2901_ = lean_mk_array(v___x_2900_, v_a_2898_);
v___x_2902_ = l_Array_append___redArg(v_xs_2899_, v___x_2901_);
lean_dec_ref(v___x_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Vector_rightpad___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_m_2904_, lean_object* v_n_2905_, lean_object* v_a_2906_, lean_object* v_xs_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Vector_rightpad(v_00_u03b1_2903_, v_m_2904_, v_n_2905_, v_a_2906_, v_xs_2907_);
lean_dec(v_n_2905_);
lean_dec(v_m_2904_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object* v_f_2909_, lean_object* v_a_2910_, lean_object* v_h_2911_, lean_object* v_b_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_apply_3(v_f_2909_, v_a_2910_, lean_box(0), v_b_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1(lean_object* v_inst_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_xs_2916_, lean_object* v_b_2917_, lean_object* v_f_2918_){
_start:
{
lean_object* v___f_2919_; size_t v_sz_2920_; size_t v___x_2921_; lean_object* v___x_2922_; 
v___f_2919_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2919_, 0, v_f_2918_);
v_sz_2920_ = lean_array_size(v_xs_2916_);
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2914_, v_xs_2916_, v___f_2919_, v_sz_2920_, v___x_2921_, v_b_2917_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg(lean_object* v_inst_2923_){
_start:
{
lean_object* v___f_2924_; 
v___f_2924_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2924_, 0, v_inst_2923_);
return v___f_2924_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad(lean_object* v_m_2925_, lean_object* v_00_u03b1_2926_, lean_object* v_n_2927_, lean_object* v_inst_2928_){
_start:
{
lean_object* v___f_2929_; 
v___f_2929_ = lean_alloc_closure((void*)(l_Vector_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2929_, 0, v_inst_2928_);
return v___f_2929_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForIn_x27InferInstanceMembershipOfMonad___boxed(lean_object* v_m_2930_, lean_object* v_00_u03b1_2931_, lean_object* v_n_2932_, lean_object* v_inst_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Vector_instForIn_x27InferInstanceMembershipOfMonad(v_m_2930_, v_00_u03b1_2931_, v_n_2932_, v_inst_2933_);
lean_dec(v_n_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad___redArg(lean_object* v_n_2935_, lean_object* v_inst_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2937_, 0, lean_box(0));
lean_closure_set(v___x_2937_, 1, lean_box(0));
lean_closure_set(v___x_2937_, 2, v_n_2935_);
lean_closure_set(v___x_2937_, 3, v_inst_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Vector_instForMOfMonad(lean_object* v_m_2938_, lean_object* v_00_u03b1_2939_, lean_object* v_n_2940_, lean_object* v_inst_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_closure((void*)(l_Vector_forM___boxed), 6, 4);
lean_closure_set(v___x_2942_, 0, lean_box(0));
lean_closure_set(v___x_2942_, 1, lean_box(0));
lean_closure_set(v___x_2942_, 2, v_n_2940_);
lean_closure_set(v___x_2942_, 3, v_inst_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT(lean_object* v_00_u03b1_2943_, lean_object* v_n_2944_, lean_object* v_inst_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = lean_box(0);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLT___boxed(lean_object* v_00_u03b1_2947_, lean_object* v_n_2948_, lean_object* v_inst_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Vector_instLT(v_00_u03b1_2947_, v_n_2948_, v_inst_2949_);
lean_dec(v_n_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE(lean_object* v_00_u03b1_2951_, lean_object* v_n_2952_, lean_object* v_inst_2953_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = lean_box(0);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Vector_instLE___boxed(lean_object* v_00_u03b1_2955_, lean_object* v_n_2956_, lean_object* v_inst_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Vector_instLE(v_00_u03b1_2955_, v_n_2956_, v_inst_2957_);
lean_dec(v_n_2956_);
return v_res_2958_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__2(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = ((lean_object*)(l_Vector_lex___auto__1___closed__0));
v___x_2966_ = l_Lean_mkAtom(v___x_2965_);
return v___x_2966_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__3(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = lean_obj_once(&l_Vector_lex___auto__1___closed__2, &l_Vector_lex___auto__1___closed__2_once, _init_l_Vector_lex___auto__1___closed__2);
v___x_2968_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2969_ = lean_array_push(v___x_2968_, v___x_2967_);
return v___x_2969_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__8(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__17));
v___x_2983_ = l_Lean_mkAtom(v___x_2982_);
return v___x_2983_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2984_ = lean_obj_once(&l_Vector_lex___auto__1___closed__8, &l_Vector_lex___auto__1___closed__8_once, _init_l_Vector_lex___auto__1___closed__8);
v___x_2985_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_2986_ = lean_array_push(v___x_2985_, v___x_2984_);
return v___x_2986_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2992_ = lean_string_utf8_byte_size(v___x_2991_);
return v___x_2992_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__14(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2993_ = lean_obj_once(&l_Vector_lex___auto__1___closed__13, &l_Vector_lex___auto__1___closed__13_once, _init_l_Vector_lex___auto__1___closed__13);
v___x_2994_ = lean_unsigned_to_nat(0u);
v___x_2995_ = ((lean_object*)(l_Vector_lex___auto__1___closed__12));
v___x_2996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
lean_ctor_set(v___x_2996_, 1, v___x_2994_);
lean_ctor_set(v___x_2996_, 2, v___x_2993_);
return v___x_2996_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_obj_once(&l_Vector_lex___auto__1___closed__14, &l_Vector_lex___auto__1___closed__14_once, _init_l_Vector_lex___auto__1___closed__14);
v___x_3000_ = lean_box(2);
v___x_3001_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
lean_ctor_set(v___x_3001_, 1, v___x_2999_);
lean_ctor_set(v___x_3001_, 2, v___x_2998_);
lean_ctor_set(v___x_3001_, 3, v___x_2997_);
return v___x_3001_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__16(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3002_ = lean_obj_once(&l_Vector_lex___auto__1___closed__15, &l_Vector_lex___auto__1___closed__15_once, _init_l_Vector_lex___auto__1___closed__15);
v___x_3003_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3004_ = lean_array_push(v___x_3003_, v___x_3002_);
return v___x_3004_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__17(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = lean_obj_once(&l_Vector_lex___auto__1___closed__16, &l_Vector_lex___auto__1___closed__16_once, _init_l_Vector_lex___auto__1___closed__16);
v___x_3006_ = ((lean_object*)(l_Vector_lex___auto__1___closed__11));
v___x_3007_ = lean_box(2);
v___x_3008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
lean_ctor_set(v___x_3008_, 1, v___x_3006_);
lean_ctor_set(v___x_3008_, 2, v___x_3005_);
return v___x_3008_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__18(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3010_ = lean_obj_once(&l_Vector_lex___auto__1___closed__9, &l_Vector_lex___auto__1___closed__9_once, _init_l_Vector_lex___auto__1___closed__9);
v___x_3011_ = lean_array_push(v___x_3010_, v___x_3009_);
return v___x_3011_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__19(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3012_ = lean_obj_once(&l_Vector_lex___auto__1___closed__18, &l_Vector_lex___auto__1___closed__18_once, _init_l_Vector_lex___auto__1___closed__18);
v___x_3013_ = ((lean_object*)(l_Vector_lex___auto__1___closed__7));
v___x_3014_ = lean_box(2);
v___x_3015_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v___x_3013_);
lean_ctor_set(v___x_3015_, 2, v___x_3012_);
return v___x_3015_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = lean_obj_once(&l_Vector_lex___auto__1___closed__19, &l_Vector_lex___auto__1___closed__19_once, _init_l_Vector_lex___auto__1___closed__19);
v___x_3017_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3018_ = lean_array_push(v___x_3017_, v___x_3016_);
return v___x_3018_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__26(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = ((lean_object*)(l_Vector_lex___auto__1___closed__25));
v___x_3030_ = l_Lean_mkAtom(v___x_3029_);
return v___x_3030_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = lean_obj_once(&l_Vector_lex___auto__1___closed__26, &l_Vector_lex___auto__1___closed__26_once, _init_l_Vector_lex___auto__1___closed__26);
v___x_3032_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3033_ = lean_array_push(v___x_3032_, v___x_3031_);
return v___x_3033_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_obj_once(&l_Vector_lex___auto__1___closed__17, &l_Vector_lex___auto__1___closed__17_once, _init_l_Vector_lex___auto__1___closed__17);
v___x_3035_ = lean_obj_once(&l_Vector_lex___auto__1___closed__27, &l_Vector_lex___auto__1___closed__27_once, _init_l_Vector_lex___auto__1___closed__27);
v___x_3036_ = lean_array_push(v___x_3035_, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3037_ = lean_obj_once(&l_Vector_lex___auto__1___closed__28, &l_Vector_lex___auto__1___closed__28_once, _init_l_Vector_lex___auto__1___closed__28);
v___x_3038_ = ((lean_object*)(l_Vector_lex___auto__1___closed__24));
v___x_3039_ = lean_box(2);
v___x_3040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3038_);
lean_ctor_set(v___x_3040_, 2, v___x_3037_);
return v___x_3040_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3042_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3043_ = lean_array_push(v___x_3042_, v___x_3041_);
return v___x_3043_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__32(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = ((lean_object*)(l_Vector_lex___auto__1___closed__31));
v___x_3046_ = l_Lean_mkAtom(v___x_3045_);
return v___x_3046_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__33(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = lean_obj_once(&l_Vector_lex___auto__1___closed__32, &l_Vector_lex___auto__1___closed__32_once, _init_l_Vector_lex___auto__1___closed__32);
v___x_3048_ = lean_obj_once(&l_Vector_lex___auto__1___closed__30, &l_Vector_lex___auto__1___closed__30_once, _init_l_Vector_lex___auto__1___closed__30);
v___x_3049_ = lean_array_push(v___x_3048_, v___x_3047_);
return v___x_3049_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__34(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_obj_once(&l_Vector_lex___auto__1___closed__29, &l_Vector_lex___auto__1___closed__29_once, _init_l_Vector_lex___auto__1___closed__29);
v___x_3051_ = lean_obj_once(&l_Vector_lex___auto__1___closed__33, &l_Vector_lex___auto__1___closed__33_once, _init_l_Vector_lex___auto__1___closed__33);
v___x_3052_ = lean_array_push(v___x_3051_, v___x_3050_);
return v___x_3052_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__35(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = lean_obj_once(&l_Vector_lex___auto__1___closed__34, &l_Vector_lex___auto__1___closed__34_once, _init_l_Vector_lex___auto__1___closed__34);
v___x_3054_ = ((lean_object*)(l_Vector_lex___auto__1___closed__22));
v___x_3055_ = lean_box(2);
v___x_3056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v___x_3054_);
lean_ctor_set(v___x_3056_, 2, v___x_3053_);
return v___x_3056_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__36(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_obj_once(&l_Vector_lex___auto__1___closed__35, &l_Vector_lex___auto__1___closed__35_once, _init_l_Vector_lex___auto__1___closed__35);
v___x_3058_ = lean_obj_once(&l_Vector_lex___auto__1___closed__20, &l_Vector_lex___auto__1___closed__20_once, _init_l_Vector_lex___auto__1___closed__20);
v___x_3059_ = lean_array_push(v___x_3058_, v___x_3057_);
return v___x_3059_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__22));
v___x_3061_ = l_Lean_mkAtom(v___x_3060_);
return v___x_3061_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = lean_obj_once(&l_Vector_lex___auto__1___closed__37, &l_Vector_lex___auto__1___closed__37_once, _init_l_Vector_lex___auto__1___closed__37);
v___x_3063_ = lean_obj_once(&l_Vector_lex___auto__1___closed__36, &l_Vector_lex___auto__1___closed__36_once, _init_l_Vector_lex___auto__1___closed__36);
v___x_3064_ = lean_array_push(v___x_3063_, v___x_3062_);
return v___x_3064_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3065_ = lean_obj_once(&l_Vector_lex___auto__1___closed__38, &l_Vector_lex___auto__1___closed__38_once, _init_l_Vector_lex___auto__1___closed__38);
v___x_3066_ = ((lean_object*)(l_Vector_lex___auto__1___closed__5));
v___x_3067_ = lean_box(2);
v___x_3068_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3066_);
lean_ctor_set(v___x_3068_, 2, v___x_3065_);
return v___x_3068_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = lean_obj_once(&l_Vector_lex___auto__1___closed__39, &l_Vector_lex___auto__1___closed__39_once, _init_l_Vector_lex___auto__1___closed__39);
v___x_3070_ = lean_obj_once(&l_Vector_lex___auto__1___closed__3, &l_Vector_lex___auto__1___closed__3_once, _init_l_Vector_lex___auto__1___closed__3);
v___x_3071_ = lean_array_push(v___x_3070_, v___x_3069_);
return v___x_3071_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3072_ = lean_obj_once(&l_Vector_lex___auto__1___closed__40, &l_Vector_lex___auto__1___closed__40_once, _init_l_Vector_lex___auto__1___closed__40);
v___x_3073_ = ((lean_object*)(l_Vector_lex___auto__1___closed__1));
v___x_3074_ = lean_box(2);
v___x_3075_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
lean_ctor_set(v___x_3075_, 2, v___x_3072_);
return v___x_3075_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__42(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_Vector_lex___auto__1___closed__41, &l_Vector_lex___auto__1___closed__41_once, _init_l_Vector_lex___auto__1___closed__41);
v___x_3077_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3078_ = lean_array_push(v___x_3077_, v___x_3076_);
return v___x_3078_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3079_ = lean_obj_once(&l_Vector_lex___auto__1___closed__42, &l_Vector_lex___auto__1___closed__42_once, _init_l_Vector_lex___auto__1___closed__42);
v___x_3080_ = ((lean_object*)(l_Vector___aux__Init__Data__Vector__Basic______macroRules__Vector__term_x23v_x5b___x2c_x5d__1___closed__14));
v___x_3081_ = lean_box(2);
v___x_3082_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
lean_ctor_set(v___x_3082_, 2, v___x_3079_);
return v___x_3082_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Vector_lex___auto__1___closed__43, &l_Vector_lex___auto__1___closed__43_once, _init_l_Vector_lex___auto__1___closed__43);
v___x_3084_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3085_ = lean_array_push(v___x_3084_, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3086_ = lean_obj_once(&l_Vector_lex___auto__1___closed__44, &l_Vector_lex___auto__1___closed__44_once, _init_l_Vector_lex___auto__1___closed__44);
v___x_3087_ = ((lean_object*)(l_Vector_set___auto__1___closed__5));
v___x_3088_ = lean_box(2);
v___x_3089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
lean_ctor_set(v___x_3089_, 1, v___x_3087_);
lean_ctor_set(v___x_3089_, 2, v___x_3086_);
return v___x_3089_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_obj_once(&l_Vector_lex___auto__1___closed__45, &l_Vector_lex___auto__1___closed__45_once, _init_l_Vector_lex___auto__1___closed__45);
v___x_3091_ = ((lean_object*)(l_Vector_set___auto__1___closed__3));
v___x_3092_ = lean_array_push(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l_Vector_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3093_ = lean_obj_once(&l_Vector_lex___auto__1___closed__46, &l_Vector_lex___auto__1___closed__46_once, _init_l_Vector_lex___auto__1___closed__46);
v___x_3094_ = ((lean_object*)(l_Vector_set___auto__1___closed__2));
v___x_3095_ = lean_box(2);
v___x_3096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v___x_3094_);
lean_ctor_set(v___x_3096_, 2, v___x_3093_);
return v___x_3096_;
}
}
static lean_object* _init_l_Vector_lex___auto__1(void){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = lean_obj_once(&l_Vector_lex___auto__1___closed__47, &l_Vector_lex___auto__1___closed__47_once, _init_l_Vector_lex___auto__1___closed__47);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0(lean_object* v_n_3098_, lean_object* v_xs_3099_, lean_object* v_ys_3100_, lean_object* v_lt_3101_, lean_object* v_inst_3102_, lean_object* v___x_3103_, lean_object* v___x_3104_, lean_object* v_next_3105_, lean_object* v_acc_3106_, lean_object* v_h_3107_, lean_object* v_G_3108_){
_start:
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_nat_dec_lt(v_next_3105_, v_n_3098_);
if (v___x_3109_ == 0)
{
lean_dec_ref(v_G_3108_);
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_inst_3102_);
lean_dec_ref(v_lt_3101_);
lean_inc_ref(v_acc_3106_);
return v_acc_3106_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v___x_3110_ = lean_array_fget_borrowed(v_xs_3099_, v_next_3105_);
v___x_3111_ = lean_array_fget_borrowed(v_ys_3100_, v_next_3105_);
lean_inc(v___x_3111_);
lean_inc(v___x_3110_);
v___x_3112_ = lean_apply_2(v_lt_3101_, v___x_3110_, v___x_3111_);
v___x_3113_ = lean_unbox(v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
lean_inc(v___x_3111_);
lean_inc(v___x_3110_);
v___x_3114_ = lean_apply_2(v_inst_3102_, v___x_3110_, v___x_3111_);
v___x_3115_ = lean_unbox(v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v_G_3108_);
lean_dec_ref(v___x_3104_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3112_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v___x_3103_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_add(v_next_3105_, v___x_3118_);
v___x_3120_ = lean_apply_4(v_G_3108_, v___x_3119_, v___x_3104_, lean_box(0), lean_box(0));
return v___x_3120_;
}
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v_G_3108_);
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_inst_3102_);
v___x_3121_ = lean_box(v___x_3109_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___x_3103_);
return v___x_3123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___lam__0___boxed(lean_object* v_n_3124_, lean_object* v_xs_3125_, lean_object* v_ys_3126_, lean_object* v_lt_3127_, lean_object* v_inst_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v_next_3131_, lean_object* v_acc_3132_, lean_object* v_h_3133_, lean_object* v_G_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Vector_lex___redArg___lam__0(v_n_3124_, v_xs_3125_, v_ys_3126_, v_lt_3127_, v_inst_3128_, v___x_3129_, v___x_3130_, v_next_3131_, v_acc_3132_, v_h_3133_, v_G_3134_);
lean_dec_ref(v_acc_3132_);
lean_dec(v_next_3131_);
lean_dec_ref(v_ys_3126_);
lean_dec_ref(v_xs_3125_);
lean_dec(v_n_3124_);
return v_res_3135_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex___redArg(lean_object* v_n_3139_, lean_object* v_inst_3140_, lean_object* v_xs_3141_, lean_object* v_ys_3142_, lean_object* v_lt_3143_){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___f_3147_; lean_object* v___x_3148_; lean_object* v_fst_3149_; 
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_box(0);
v___x_3146_ = ((lean_object*)(l_Vector_lex___redArg___closed__0));
v___f_3147_ = lean_alloc_closure((void*)(l_Vector_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_3147_, 0, v_n_3139_);
lean_closure_set(v___f_3147_, 1, v_xs_3141_);
lean_closure_set(v___f_3147_, 2, v_ys_3142_);
lean_closure_set(v___f_3147_, 3, v_lt_3143_);
lean_closure_set(v___f_3147_, 4, v_inst_3140_);
lean_closure_set(v___f_3147_, 5, v___x_3145_);
lean_closure_set(v___f_3147_, 6, v___x_3146_);
v___x_3148_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3147_, v___x_3144_, v___x_3146_, lean_box(0));
v_fst_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_fst_3149_);
lean_dec(v___x_3148_);
if (lean_obj_tag(v_fst_3149_) == 0)
{
uint8_t v___x_3150_; 
v___x_3150_ = 0;
return v___x_3150_;
}
else
{
lean_object* v_val_3151_; uint8_t v___x_3152_; 
v_val_3151_ = lean_ctor_get(v_fst_3149_, 0);
lean_inc(v_val_3151_);
lean_dec_ref_known(v_fst_3149_, 1);
v___x_3152_ = lean_unbox(v_val_3151_);
lean_dec(v_val_3151_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l_Vector_lex___redArg___boxed(lean_object* v_n_3153_, lean_object* v_inst_3154_, lean_object* v_xs_3155_, lean_object* v_ys_3156_, lean_object* v_lt_3157_){
_start:
{
uint8_t v_res_3158_; lean_object* v_r_3159_; 
v_res_3158_ = l_Vector_lex___redArg(v_n_3153_, v_inst_3154_, v_xs_3155_, v_ys_3156_, v_lt_3157_);
v_r_3159_ = lean_box(v_res_3158_);
return v_r_3159_;
}
}
LEAN_EXPORT uint8_t l_Vector_lex(lean_object* v_00_u03b1_3160_, lean_object* v_n_3161_, lean_object* v_inst_3162_, lean_object* v_xs_3163_, lean_object* v_ys_3164_, lean_object* v_lt_3165_){
_start:
{
uint8_t v___x_3166_; 
v___x_3166_ = l_Vector_lex___redArg(v_n_3161_, v_inst_3162_, v_xs_3163_, v_ys_3164_, v_lt_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Vector_lex___boxed(lean_object* v_00_u03b1_3167_, lean_object* v_n_3168_, lean_object* v_inst_3169_, lean_object* v_xs_3170_, lean_object* v_ys_3171_, lean_object* v_lt_3172_){
_start:
{
uint8_t v_res_3173_; lean_object* v_r_3174_; 
v_res_3173_ = l_Vector_lex(v_00_u03b1_3167_, v_n_3168_, v_inst_3169_, v_xs_3170_, v_ys_3171_, v_lt_3172_);
v_r_3174_ = lean_box(v_res_3173_);
return v_r_3174_;
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
