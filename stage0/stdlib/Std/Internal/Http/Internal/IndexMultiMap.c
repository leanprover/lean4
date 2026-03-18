// Lean compiler output
// Module: Std.Internal.Http.Internal.IndexMultiMap
// Imports: public import Init.Grind public import Init.Data.Int.OfNat public import Std.Data.HashMap
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mapFinIdxM_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instRepr___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37_value;
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__0 = (const lean_object*)&l_Std_Internal_instInhabitedIndexMultiMap___closed__0_value;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__1;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__2;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0_value;
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1_value;
static const lean_string_object l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2 = (const lean_object*)&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(lean_object* v_a_1_, lean_object* v_b_2_, lean_object* v_d_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_a_1_);
lean_ctor_set(v___x_4_, 1, v_b_2_);
v___x_5_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_d_3_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__1(lean_object* v___x_6_, lean_object* v___f_7_, lean_object* v_l_8_, lean_object* v_acc_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_6_, v___f_7_, v_acc_9_, v_l_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(11u);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18));
v___x_67_ = lean_string_length(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32);
v___x_69_ = lean_nat_to_int(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg(lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_entries_81_; lean_object* v_indexes_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_147_; 
v_entries_81_ = lean_ctor_get(v_x_80_, 0);
v_indexes_82_ = lean_ctor_get(v_x_80_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_147_ == 0)
{
v___x_84_ = v_x_80_;
v_isShared_85_ = v_isSharedCheck_147_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_indexes_82_);
lean_inc(v_entries_81_);
lean_dec(v_x_80_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_147_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v_buckets_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_145_; 
v___x_86_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_buckets_87_ = lean_ctor_get(v_indexes_82_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_indexes_82_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_indexes_82_, 0);
lean_dec(v_unused_146_);
v___x_89_ = v_indexes_82_;
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_buckets_87_);
lean_dec(v_indexes_82_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_145_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_91_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14));
v___x_92_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15));
v___f_93_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_93_, 0, v_inst_79_);
lean_inc_ref(v_inst_78_);
v___x_94_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_94_, 0, lean_box(0));
lean_closure_set(v___x_94_, 1, lean_box(0));
lean_closure_set(v___x_94_, 2, v_inst_78_);
lean_closure_set(v___x_94_, 3, v___f_93_);
v___x_95_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19);
v___x_96_ = l_Array_repr___redArg(v___x_94_, v_entries_81_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 4);
lean_ctor_set(v___x_89_, 1, v___x_96_);
lean_ctor_set(v___x_89_, 0, v___x_95_);
v___x_98_ = v___x_89_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_144_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
if (v_isShared_85_ == 0)
{
lean_ctor_set_tag(v___x_84_, 5);
lean_ctor_set(v___x_84_, 1, v___x_100_);
lean_ctor_set(v___x_84_, 0, v___x_92_);
v___x_102_ = v___x_84_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_143_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___y_115_; lean_object* v___x_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_103_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21));
v___x_104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
v___x_105_ = lean_box(1);
v___x_106_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23));
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_91_);
v___f_110_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24));
v___x_111_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_111_, 0, lean_box(0));
lean_closure_set(v___x_111_, 1, lean_box(0));
lean_closure_set(v___x_111_, 2, v_inst_78_);
lean_closure_set(v___x_111_, 3, v___f_110_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26));
v___x_136_ = lean_box(0);
v___x_137_ = lean_array_get_size(v_buckets_87_);
v___x_138_ = lean_nat_dec_lt(v___x_112_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v_buckets_87_);
v___y_115_ = v___x_136_;
goto v___jp_114_;
}
else
{
lean_object* v___f_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v___x_142_; 
v___f_139_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__37));
v___x_140_ = lean_usize_of_nat(v___x_137_);
v___x_141_ = ((size_t)0ULL);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_86_, v___f_139_, v_buckets_87_, v___x_140_, v___x_141_, v___x_136_);
v___y_115_ = v___x_142_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_116_ = l_List_repr___redArg(v___x_111_, v___y_115_);
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_113_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v___x_112_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_95_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_99_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_109_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_103_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_105_);
v___x_124_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28));
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_91_);
v___x_127_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30));
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33);
v___x_130_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34));
v___x_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_128_);
v___x_132_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35));
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_129_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_99_);
return v___x_135_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_x_154_, lean_object* v_prec_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg(v_inst_152_, v_inst_153_, v_x_154_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___boxed(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_x_163_, lean_object* v_prec_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_Internal_instReprIndexMultiMap_repr(v_00_u03b1_157_, v_00_u03b2_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_inst_162_, v_x_163_, v_prec_164_);
lean_dec(v_prec_164_);
lean_dec_ref(v_inst_160_);
lean_dec_ref(v_inst_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap___redArg(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_170_, 0, lean_box(0));
lean_closure_set(v___x_170_, 1, lean_box(0));
lean_closure_set(v___x_170_, 2, v_inst_166_);
lean_closure_set(v___x_170_, 3, v_inst_167_);
lean_closure_set(v___x_170_, 4, v_inst_168_);
lean_closure_set(v___x_170_, 5, v_inst_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_177_, 0, lean_box(0));
lean_closure_set(v___x_177_, 1, lean_box(0));
lean_closure_set(v___x_177_, 2, v_inst_173_);
lean_closure_set(v___x_177_, 3, v_inst_174_);
lean_closure_set(v___x_177_, 4, v_inst_175_);
lean_closure_set(v___x_177_, 5, v_inst_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(16u);
v___x_182_ = lean_mk_array(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__1, &l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__2, &l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2);
v___x_187_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_196_, v_00_u03b2_197_, v_inst_198_, v_inst_199_, v_inst_200_, v_inst_201_);
lean_dec(v_inst_201_);
lean_dec(v_inst_200_);
lean_dec_ref(v_inst_199_);
lean_dec_ref(v_inst_198_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_208_, v_00_u03b2_209_, v_inst_210_, v_inst_211_);
lean_dec_ref(v_inst_211_);
lean_dec_ref(v_inst_210_);
return v_res_212_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_key_215_, lean_object* v_map_216_){
_start:
{
lean_object* v_indexes_217_; uint8_t v___x_218_; 
v_indexes_217_ = lean_ctor_get(v_map_216_, 1);
v___x_218_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_213_, v_inst_214_, v_indexes_217_, v_key_215_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_key_221_, lean_object* v_map_222_){
_start:
{
uint8_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_219_, v_inst_220_, v_key_221_, v_map_222_);
lean_dec_ref(v_map_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_key_229_, lean_object* v_map_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_227_, v_inst_228_, v_key_229_, v_map_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_key_236_, lean_object* v_map_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_232_, v_00_u03b2_233_, v_inst_234_, v_inst_235_, v_key_236_, v_map_237_);
lean_dec_ref(v_map_237_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v___x_240_, lean_object* v_entries_241_, lean_object* v_x1_242_, lean_object* v_x2_243_, lean_object* v_x3_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_snd_247_; 
v___x_245_ = lean_array_fget_borrowed(v___x_240_, v_x1_242_);
v___x_246_ = lean_array_fget_borrowed(v_entries_241_, v___x_245_);
v_snd_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_snd_247_);
return v_snd_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v___x_248_, lean_object* v_entries_249_, lean_object* v_x1_250_, lean_object* v_x2_251_, lean_object* v_x3_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v___x_248_, v_entries_249_, v_x1_250_, v_x2_251_, v_x3_252_);
lean_dec(v_x2_251_);
lean_dec(v_x1_250_);
lean_dec_ref(v_entries_249_);
lean_dec_ref(v___x_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_map_256_, lean_object* v_key_257_){
_start:
{
lean_object* v_entries_258_; lean_object* v_indexes_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_entries_266_; 
v_entries_258_ = lean_ctor_get(v_map_256_, 0);
lean_inc_ref(v_entries_258_);
v_indexes_259_ = lean_ctor_get(v_map_256_, 1);
lean_inc_ref(v_indexes_259_);
lean_dec_ref(v_map_256_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_254_, v_inst_255_, v_indexes_259_, v_key_257_);
lean_dec_ref(v_indexes_259_);
lean_inc(v___x_260_);
v___f_261_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_261_, 0, v___x_260_);
lean_closure_set(v___f_261_, 1, v_entries_258_);
v___x_262_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_263_ = lean_array_get_size(v___x_260_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_263_);
v_entries_266_ = l_Array_mapFinIdxM_map___redArg(v___x_262_, v___x_260_, v___f_261_, v___x_263_, v___x_264_, v___x_265_);
return v_entries_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_267_, lean_object* v_00_u03b2_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_map_271_, lean_object* v_key_272_, lean_object* v_h_273_){
_start:
{
lean_object* v_entries_274_; lean_object* v_indexes_275_; lean_object* v___x_276_; lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_entries_282_; 
v_entries_274_ = lean_ctor_get(v_map_271_, 0);
lean_inc_ref(v_entries_274_);
v_indexes_275_ = lean_ctor_get(v_map_271_, 1);
lean_inc_ref(v_indexes_275_);
lean_dec_ref(v_map_271_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_269_, v_inst_270_, v_indexes_275_, v_key_272_);
lean_dec_ref(v_indexes_275_);
lean_inc(v___x_276_);
v___f_277_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_277_, 0, v___x_276_);
lean_closure_set(v___f_277_, 1, v_entries_274_);
v___x_278_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_279_ = lean_array_get_size(v___x_276_);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_mk_empty_array_with_capacity(v___x_279_);
v_entries_282_ = l_Array_mapFinIdxM_map___redArg(v___x_278_, v___x_276_, v___f_277_, v___x_279_, v___x_280_, v___x_281_);
return v_entries_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_map_285_, lean_object* v_key_286_){
_start:
{
lean_object* v_entries_287_; lean_object* v_indexes_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_entry_291_; lean_object* v___x_292_; lean_object* v_snd_293_; 
v_entries_287_ = lean_ctor_get(v_map_285_, 0);
v_indexes_288_ = lean_ctor_get(v_map_285_, 1);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_283_, v_inst_284_, v_indexes_288_, v_key_286_);
v___x_290_ = lean_unsigned_to_nat(0u);
v_entry_291_ = lean_array_fget(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_array_fget_borrowed(v_entries_287_, v_entry_291_);
lean_dec(v_entry_291_);
v_snd_293_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_snd_293_);
return v_snd_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_map_296_, lean_object* v_key_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_294_, v_inst_295_, v_map_296_, v_key_297_);
lean_dec_ref(v_map_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_299_, lean_object* v_00_u03b2_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_map_303_, lean_object* v_key_304_, lean_object* v_h_305_){
_start:
{
lean_object* v_entries_306_; lean_object* v_indexes_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_entry_310_; lean_object* v___x_311_; lean_object* v_snd_312_; 
v_entries_306_ = lean_ctor_get(v_map_303_, 0);
v_indexes_307_ = lean_ctor_get(v_map_303_, 1);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_301_, v_inst_302_, v_indexes_307_, v_key_304_);
v___x_309_ = lean_unsigned_to_nat(0u);
v_entry_310_ = lean_array_fget(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_array_fget_borrowed(v_entries_306_, v_entry_310_);
lean_dec(v_entry_310_);
v_snd_312_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_snd_312_);
return v_snd_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_313_, lean_object* v_00_u03b2_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_map_317_, lean_object* v_key_318_, lean_object* v_h_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_313_, v_00_u03b2_314_, v_inst_315_, v_inst_316_, v_map_317_, v_key_318_, v_h_319_);
lean_dec_ref(v_map_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_map_323_, lean_object* v_key_324_){
_start:
{
uint8_t v___x_325_; 
lean_inc(v_key_324_);
lean_inc_ref(v_inst_322_);
lean_inc_ref(v_inst_321_);
v___x_325_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_321_, v_inst_322_, v_key_324_, v_map_323_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_key_324_);
lean_dec_ref(v_map_323_);
lean_dec_ref(v_inst_322_);
lean_dec_ref(v_inst_321_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v_entries_327_; lean_object* v_indexes_328_; lean_object* v___x_329_; lean_object* v___f_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v_entries_335_; lean_object* v___x_336_; 
v_entries_327_ = lean_ctor_get(v_map_323_, 0);
lean_inc_ref(v_entries_327_);
v_indexes_328_ = lean_ctor_get(v_map_323_, 1);
lean_inc_ref(v_indexes_328_);
lean_dec_ref(v_map_323_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_321_, v_inst_322_, v_indexes_328_, v_key_324_);
lean_dec_ref(v_indexes_328_);
lean_inc(v___x_329_);
v___f_330_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_330_, 0, v___x_329_);
lean_closure_set(v___f_330_, 1, v_entries_327_);
v___x_331_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_332_ = lean_array_get_size(v___x_329_);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_332_);
v_entries_335_ = l_Array_mapFinIdxM_map___redArg(v___x_331_, v___x_329_, v___f_330_, v___x_332_, v___x_333_, v___x_334_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v_entries_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_337_, lean_object* v_00_u03b2_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_map_341_, lean_object* v_key_342_){
_start:
{
uint8_t v___x_343_; 
lean_inc(v_key_342_);
lean_inc_ref(v_inst_340_);
lean_inc_ref(v_inst_339_);
v___x_343_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_339_, v_inst_340_, v_key_342_, v_map_341_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
lean_dec(v_key_342_);
lean_dec_ref(v_map_341_);
lean_dec_ref(v_inst_340_);
lean_dec_ref(v_inst_339_);
v___x_344_ = lean_box(0);
return v___x_344_;
}
else
{
lean_object* v_entries_345_; lean_object* v_indexes_346_; lean_object* v___x_347_; lean_object* v___f_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_entries_353_; lean_object* v___x_354_; 
v_entries_345_ = lean_ctor_get(v_map_341_, 0);
lean_inc_ref(v_entries_345_);
v_indexes_346_ = lean_ctor_get(v_map_341_, 1);
lean_inc_ref(v_indexes_346_);
lean_dec_ref(v_map_341_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_339_, v_inst_340_, v_indexes_346_, v_key_342_);
lean_dec_ref(v_indexes_346_);
lean_inc(v___x_347_);
v___f_348_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_348_, 0, v___x_347_);
lean_closure_set(v___f_348_, 1, v_entries_345_);
v___x_349_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_350_ = lean_array_get_size(v___x_347_);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_350_);
v_entries_353_ = l_Array_mapFinIdxM_map___redArg(v___x_349_, v___x_347_, v___f_348_, v___x_350_, v___x_351_, v___x_352_);
v___x_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_354_, 0, v_entries_353_);
return v___x_354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_map_357_, lean_object* v_key_358_){
_start:
{
uint8_t v___x_359_; 
lean_inc(v_key_358_);
lean_inc_ref(v_inst_356_);
lean_inc_ref(v_inst_355_);
v___x_359_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_355_, v_inst_356_, v_key_358_, v_map_357_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
lean_dec(v_key_358_);
lean_dec_ref(v_inst_356_);
lean_dec_ref(v_inst_355_);
v___x_360_ = lean_box(0);
return v___x_360_;
}
else
{
lean_object* v_entries_361_; lean_object* v_indexes_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_entry_365_; lean_object* v___x_366_; lean_object* v_snd_367_; lean_object* v___x_368_; 
v_entries_361_ = lean_ctor_get(v_map_357_, 0);
v_indexes_362_ = lean_ctor_get(v_map_357_, 1);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_355_, v_inst_356_, v_indexes_362_, v_key_358_);
v___x_364_ = lean_unsigned_to_nat(0u);
v_entry_365_ = lean_array_fget(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_array_fget_borrowed(v_entries_361_, v_entry_365_);
lean_dec(v_entry_365_);
v_snd_367_ = lean_ctor_get(v___x_366_, 1);
lean_inc(v_snd_367_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v_snd_367_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_map_371_, lean_object* v_key_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_369_, v_inst_370_, v_map_371_, v_key_372_);
lean_dec_ref(v_map_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_map_378_, lean_object* v_key_379_){
_start:
{
uint8_t v___x_380_; 
lean_inc(v_key_379_);
lean_inc_ref(v_inst_377_);
lean_inc_ref(v_inst_376_);
v___x_380_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_376_, v_inst_377_, v_key_379_, v_map_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
lean_dec(v_key_379_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v_entries_382_; lean_object* v_indexes_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_entry_386_; lean_object* v___x_387_; lean_object* v_snd_388_; lean_object* v___x_389_; 
v_entries_382_ = lean_ctor_get(v_map_378_, 0);
v_indexes_383_ = lean_ctor_get(v_map_378_, 1);
v___x_384_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_376_, v_inst_377_, v_indexes_383_, v_key_379_);
v___x_385_ = lean_unsigned_to_nat(0u);
v_entry_386_ = lean_array_fget(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_array_fget_borrowed(v_entries_382_, v_entry_386_);
lean_dec(v_entry_386_);
v_snd_388_ = lean_ctor_get(v___x_387_, 1);
lean_inc(v_snd_388_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v_snd_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_map_394_, lean_object* v_key_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_390_, v_00_u03b2_391_, v_inst_392_, v_inst_393_, v_map_394_, v_key_395_);
lean_dec_ref(v_map_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_397_, lean_object* v_value_398_, lean_object* v___x_399_, lean_object* v___x_400_, lean_object* v_a_401_, lean_object* v_x_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
lean_inc(v_a_401_);
v___x_404_ = lean_apply_2(v_inst_397_, v_a_401_, v_value_398_);
v___x_405_ = lean_unbox(v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_a_401_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_399_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v___x_399_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v_a_401_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v___x_400_);
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_411_, lean_object* v_value_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v_a_415_, lean_object* v_x_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_411_, v_value_412_, v___x_413_, v___x_414_, v_a_415_, v_x_416_, v___y_417_);
lean_dec_ref(v___y_417_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_map_424_, lean_object* v_inst_425_, lean_object* v_key_426_, lean_object* v_value_427_){
_start:
{
uint8_t v___x_428_; 
lean_inc(v_key_426_);
lean_inc_ref(v_inst_423_);
lean_inc_ref(v_inst_422_);
v___x_428_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_422_, v_inst_423_, v_key_426_, v_map_424_);
if (v___x_428_ == 0)
{
lean_dec(v_value_427_);
lean_dec(v_key_426_);
lean_dec_ref(v_inst_425_);
lean_dec_ref(v_map_424_);
lean_dec_ref(v_inst_423_);
lean_dec_ref(v_inst_422_);
return v___x_428_;
}
else
{
lean_object* v_entries_429_; lean_object* v_indexes_430_; lean_object* v___x_431_; lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_entries_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___f_440_; size_t v_sz_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v_fst_444_; 
v_entries_429_ = lean_ctor_get(v_map_424_, 0);
lean_inc_ref(v_entries_429_);
v_indexes_430_ = lean_ctor_get(v_map_424_, 1);
lean_inc_ref(v_indexes_430_);
lean_dec_ref(v_map_424_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_422_, v_inst_423_, v_indexes_430_, v_key_426_);
lean_dec_ref(v_indexes_430_);
lean_inc(v___x_431_);
v___f_432_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_432_, 0, v___x_431_);
lean_closure_set(v___f_432_, 1, v_entries_429_);
v___x_433_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_434_ = lean_array_get_size(v___x_431_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_434_);
v_entries_437_ = l_Array_mapFinIdxM_map___redArg(v___x_433_, v___x_431_, v___f_432_, v___x_434_, v___x_435_, v___x_436_);
v___x_438_ = lean_box(0);
v___x_439_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_440_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_440_, 0, v_inst_425_);
lean_closure_set(v___f_440_, 1, v_value_427_);
lean_closure_set(v___f_440_, 2, v___x_439_);
lean_closure_set(v___f_440_, 3, v___x_438_);
v_sz_441_ = lean_array_size(v_entries_437_);
v___x_442_ = ((size_t)0ULL);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_433_, v_entries_437_, v___f_440_, v_sz_441_, v___x_442_, v___x_439_);
v_fst_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_fst_444_);
lean_dec(v___x_443_);
if (lean_obj_tag(v_fst_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
return v___x_445_;
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v_fst_444_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v_fst_444_);
if (lean_obj_tag(v_val_446_) == 0)
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
else
{
lean_dec_ref(v_val_446_);
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_map_450_, lean_object* v_inst_451_, lean_object* v_key_452_, lean_object* v_value_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_448_, v_inst_449_, v_map_450_, v_inst_451_, v_key_452_, v_value_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_map_460_, lean_object* v_inst_461_, lean_object* v_key_462_, lean_object* v_value_463_){
_start:
{
uint8_t v___x_464_; 
lean_inc(v_key_462_);
lean_inc_ref(v_inst_459_);
lean_inc_ref(v_inst_458_);
v___x_464_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_458_, v_inst_459_, v_key_462_, v_map_460_);
if (v___x_464_ == 0)
{
lean_dec(v_value_463_);
lean_dec(v_key_462_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_map_460_);
lean_dec_ref(v_inst_459_);
lean_dec_ref(v_inst_458_);
return v___x_464_;
}
else
{
lean_object* v_entries_465_; lean_object* v_indexes_466_; lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_entries_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___f_476_; size_t v_sz_477_; size_t v___x_478_; lean_object* v___x_479_; lean_object* v_fst_480_; 
v_entries_465_ = lean_ctor_get(v_map_460_, 0);
lean_inc_ref(v_entries_465_);
v_indexes_466_ = lean_ctor_get(v_map_460_, 1);
lean_inc_ref(v_indexes_466_);
lean_dec_ref(v_map_460_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_458_, v_inst_459_, v_indexes_466_, v_key_462_);
lean_dec_ref(v_indexes_466_);
lean_inc(v___x_467_);
v___f_468_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_468_, 0, v___x_467_);
lean_closure_set(v___f_468_, 1, v_entries_465_);
v___x_469_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_470_ = lean_array_get_size(v___x_467_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_mk_empty_array_with_capacity(v___x_470_);
v_entries_473_ = l_Array_mapFinIdxM_map___redArg(v___x_469_, v___x_467_, v___f_468_, v___x_470_, v___x_471_, v___x_472_);
v___x_474_ = lean_box(0);
v___x_475_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_476_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_476_, 0, v_inst_461_);
lean_closure_set(v___f_476_, 1, v_value_463_);
lean_closure_set(v___f_476_, 2, v___x_475_);
lean_closure_set(v___f_476_, 3, v___x_474_);
v_sz_477_ = lean_array_size(v_entries_473_);
v___x_478_ = ((size_t)0ULL);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_469_, v_entries_473_, v___f_476_, v_sz_477_, v___x_478_, v___x_475_);
v_fst_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_fst_480_);
lean_dec(v___x_479_);
if (lean_obj_tag(v_fst_480_) == 0)
{
uint8_t v___x_481_; 
v___x_481_ = 0;
return v___x_481_;
}
else
{
lean_object* v_val_482_; 
v_val_482_ = lean_ctor_get(v_fst_480_, 0);
lean_inc(v_val_482_);
lean_dec_ref(v_fst_480_);
if (lean_obj_tag(v_val_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_dec_ref(v_val_482_);
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_map_488_, lean_object* v_inst_489_, lean_object* v_key_490_, lean_object* v_value_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_484_, v_00_u03b2_485_, v_inst_486_, v_inst_487_, v_map_488_, v_inst_489_, v_key_490_, v_value_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_map_496_, lean_object* v_key_497_){
_start:
{
uint8_t v___x_498_; 
lean_inc(v_key_497_);
lean_inc_ref(v_inst_495_);
lean_inc_ref(v_inst_494_);
v___x_498_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_494_, v_inst_495_, v_key_497_, v_map_496_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_key_497_);
lean_dec_ref(v_map_496_);
lean_dec_ref(v_inst_495_);
lean_dec_ref(v_inst_494_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_entries_500_; lean_object* v_indexes_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_entries_500_ = lean_ctor_get(v_map_496_, 0);
lean_inc_ref(v_entries_500_);
v_indexes_501_ = lean_ctor_get(v_map_496_, 1);
lean_inc_ref(v_indexes_501_);
lean_dec_ref(v_map_496_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_494_, v_inst_495_, v_indexes_501_, v_key_497_);
lean_dec_ref(v_indexes_501_);
lean_inc(v___x_502_);
v___f_503_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_503_, 0, v___x_502_);
lean_closure_set(v___f_503_, 1, v_entries_500_);
v___x_504_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_505_ = lean_array_get_size(v___x_502_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_mk_empty_array_with_capacity(v___x_505_);
v_entries_508_ = l_Array_mapFinIdxM_map___redArg(v___x_504_, v___x_502_, v___f_503_, v___x_505_, v___x_506_, v___x_507_);
v___x_509_ = lean_array_get_size(v_entries_508_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_sub(v___x_509_, v___x_510_);
v___x_512_ = lean_nat_dec_lt(v___x_511_, v___x_509_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_dec(v___x_511_);
lean_dec(v_entries_508_);
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_fget(v_entries_508_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v_entries_508_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_map_520_, lean_object* v_key_521_){
_start:
{
uint8_t v___x_522_; 
lean_inc(v_key_521_);
lean_inc_ref(v_inst_519_);
lean_inc_ref(v_inst_518_);
v___x_522_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_518_, v_inst_519_, v_key_521_, v_map_520_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_key_521_);
lean_dec_ref(v_map_520_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
v___x_523_ = lean_box(0);
return v___x_523_;
}
else
{
lean_object* v_entries_524_; lean_object* v_indexes_525_; lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_entries_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_entries_524_ = lean_ctor_get(v_map_520_, 0);
lean_inc_ref(v_entries_524_);
v_indexes_525_ = lean_ctor_get(v_map_520_, 1);
lean_inc_ref(v_indexes_525_);
lean_dec_ref(v_map_520_);
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_518_, v_inst_519_, v_indexes_525_, v_key_521_);
lean_dec_ref(v_indexes_525_);
lean_inc(v___x_526_);
v___f_527_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_527_, 0, v___x_526_);
lean_closure_set(v___f_527_, 1, v_entries_524_);
v___x_528_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_529_ = lean_array_get_size(v___x_526_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_529_);
v_entries_532_ = l_Array_mapFinIdxM_map___redArg(v___x_528_, v___x_526_, v___f_527_, v___x_529_, v___x_530_, v___x_531_);
v___x_533_ = lean_array_get_size(v_entries_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_sub(v___x_533_, v___x_534_);
v___x_536_ = lean_nat_dec_lt(v___x_535_, v___x_533_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v___x_535_);
lean_dec(v_entries_532_);
v___x_537_ = lean_box(0);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_array_fget(v_entries_532_, v___x_535_);
lean_dec(v___x_535_);
lean_dec(v_entries_532_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_map_542_, lean_object* v_key_543_, lean_object* v_d_544_){
_start:
{
uint8_t v___x_545_; 
lean_inc(v_key_543_);
lean_inc_ref(v_inst_541_);
lean_inc_ref(v_inst_540_);
v___x_545_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_540_, v_inst_541_, v_key_543_, v_map_542_);
if (v___x_545_ == 0)
{
lean_dec(v_key_543_);
lean_dec_ref(v_inst_541_);
lean_dec_ref(v_inst_540_);
lean_inc(v_d_544_);
return v_d_544_;
}
else
{
lean_object* v_entries_546_; lean_object* v_indexes_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v_entry_550_; lean_object* v___x_551_; lean_object* v_snd_552_; 
v_entries_546_ = lean_ctor_get(v_map_542_, 0);
v_indexes_547_ = lean_ctor_get(v_map_542_, 1);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_540_, v_inst_541_, v_indexes_547_, v_key_543_);
v___x_549_ = lean_unsigned_to_nat(0u);
v_entry_550_ = lean_array_fget(v___x_548_, v___x_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_array_fget_borrowed(v_entries_546_, v_entry_550_);
lean_dec(v_entry_550_);
v_snd_552_ = lean_ctor_get(v___x_551_, 1);
lean_inc(v_snd_552_);
return v_snd_552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_map_555_, lean_object* v_key_556_, lean_object* v_d_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_553_, v_inst_554_, v_map_555_, v_key_556_, v_d_557_);
lean_dec(v_d_557_);
lean_dec_ref(v_map_555_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_map_563_, lean_object* v_key_564_, lean_object* v_d_565_){
_start:
{
uint8_t v___x_566_; 
lean_inc(v_key_564_);
lean_inc_ref(v_inst_562_);
lean_inc_ref(v_inst_561_);
v___x_566_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_561_, v_inst_562_, v_key_564_, v_map_563_);
if (v___x_566_ == 0)
{
lean_dec(v_key_564_);
lean_dec_ref(v_inst_562_);
lean_dec_ref(v_inst_561_);
lean_inc(v_d_565_);
return v_d_565_;
}
else
{
lean_object* v_entries_567_; lean_object* v_indexes_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_entry_571_; lean_object* v___x_572_; lean_object* v_snd_573_; 
v_entries_567_ = lean_ctor_get(v_map_563_, 0);
v_indexes_568_ = lean_ctor_get(v_map_563_, 1);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_561_, v_inst_562_, v_indexes_568_, v_key_564_);
v___x_570_ = lean_unsigned_to_nat(0u);
v_entry_571_ = lean_array_fget(v___x_569_, v___x_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_array_fget_borrowed(v_entries_567_, v_entry_571_);
lean_dec(v_entry_571_);
v_snd_573_ = lean_ctor_get(v___x_572_, 1);
lean_inc(v_snd_573_);
return v_snd_573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_inst_577_, lean_object* v_map_578_, lean_object* v_key_579_, lean_object* v_d_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_574_, v_00_u03b2_575_, v_inst_576_, v_inst_577_, v_map_578_, v_key_579_, v_d_580_);
lean_dec(v_d_580_);
lean_dec_ref(v_map_578_);
return v_res_581_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_585_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_586_ = lean_unsigned_to_nat(14u);
v___x_587_ = lean_unsigned_to_nat(22u);
v___x_588_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_589_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_590_ = l_mkPanicMessageWithDecl(v___x_589_, v___x_588_, v___x_587_, v___x_586_, v___x_585_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_map_594_, lean_object* v_key_595_){
_start:
{
uint8_t v___x_596_; 
lean_inc(v_key_595_);
lean_inc_ref(v_inst_592_);
lean_inc_ref(v_inst_591_);
v___x_596_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_591_, v_inst_592_, v_key_595_, v_map_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_key_595_);
lean_dec_ref(v_inst_592_);
lean_dec_ref(v_inst_591_);
v___x_597_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_598_ = l_panic___redArg(v_inst_593_, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v_entries_599_; lean_object* v_indexes_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_entry_603_; lean_object* v___x_604_; lean_object* v_snd_605_; 
lean_dec(v_inst_593_);
v_entries_599_ = lean_ctor_get(v_map_594_, 0);
v_indexes_600_ = lean_ctor_get(v_map_594_, 1);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_591_, v_inst_592_, v_indexes_600_, v_key_595_);
v___x_602_ = lean_unsigned_to_nat(0u);
v_entry_603_ = lean_array_fget(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_array_fget_borrowed(v_entries_599_, v_entry_603_);
lean_dec(v_entry_603_);
v_snd_605_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_605_);
return v_snd_605_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_inst_608_, lean_object* v_map_609_, lean_object* v_key_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_606_, v_inst_607_, v_inst_608_, v_map_609_, v_key_610_);
lean_dec_ref(v_map_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_612_, lean_object* v_00_u03b2_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_map_617_, lean_object* v_key_618_){
_start:
{
uint8_t v___x_619_; 
lean_inc(v_key_618_);
lean_inc_ref(v_inst_615_);
lean_inc_ref(v_inst_614_);
v___x_619_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_614_, v_inst_615_, v_key_618_, v_map_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_key_618_);
lean_dec_ref(v_inst_615_);
lean_dec_ref(v_inst_614_);
v___x_620_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_621_ = l_panic___redArg(v_inst_616_, v___x_620_);
return v___x_621_;
}
else
{
lean_object* v_entries_622_; lean_object* v_indexes_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_entry_626_; lean_object* v___x_627_; lean_object* v_snd_628_; 
lean_dec(v_inst_616_);
v_entries_622_ = lean_ctor_get(v_map_617_, 0);
v_indexes_623_ = lean_ctor_get(v_map_617_, 1);
v___x_624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_614_, v_inst_615_, v_indexes_623_, v_key_618_);
v___x_625_ = lean_unsigned_to_nat(0u);
v_entry_626_ = lean_array_fget(v___x_624_, v___x_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_array_fget_borrowed(v_entries_622_, v_entry_626_);
lean_dec(v_entry_626_);
v_snd_628_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_snd_628_);
return v_snd_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_map_634_, lean_object* v_key_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_629_, v_00_u03b2_630_, v_inst_631_, v_inst_632_, v_inst_633_, v_map_634_, v_key_635_);
lean_dec_ref(v_map_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_h__1_638_);
v___x_640_ = lean_box(0);
v___x_641_ = lean_apply_1(v_h__2_639_, v___x_640_);
return v___x_641_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_643_; 
lean_dec(v_h__2_639_);
v_val_642_ = lean_ctor_get(v_x_637_, 0);
lean_inc(v_val_642_);
lean_dec_ref(v_x_637_);
v___x_643_ = lean_apply_1(v_h__1_638_, v_val_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_644_, lean_object* v_x_645_, lean_object* v_h__1_646_, lean_object* v_h__2_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l___private_Std_Internal_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(v_x_645_, v_h__1_646_, v_h__2_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_mk_empty_array_with_capacity(v___x_651_);
v___x_653_ = lean_array_push(v___x_652_, v_i_649_);
v___x_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_val_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_val_655_ = lean_ctor_get(v_x_650_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v_x_650_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_val_655_);
lean_dec(v_x_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_array_push(v_val_655_, v_i_649_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_map_666_, lean_object* v_key_667_, lean_object* v_value_668_){
_start:
{
lean_object* v_entries_669_; lean_object* v_indexes_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_682_; 
v_entries_669_ = lean_ctor_get(v_map_666_, 0);
v_indexes_670_ = lean_ctor_get(v_map_666_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_map_666_);
if (v_isSharedCheck_682_ == 0)
{
v___x_672_ = v_map_666_;
v_isShared_673_ = v_isSharedCheck_682_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_indexes_670_);
lean_inc(v_entries_669_);
lean_dec(v_map_666_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_682_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_i_674_; lean_object* v_f_675_; lean_object* v___x_676_; lean_object* v_entries_677_; lean_object* v_indexes_678_; lean_object* v___x_680_; 
v_i_674_ = lean_array_get_size(v_entries_669_);
v_f_675_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_675_, 0, v_i_674_);
lean_inc(v_key_667_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v_key_667_);
lean_ctor_set(v___x_676_, 1, v_value_668_);
v_entries_677_ = lean_array_push(v_entries_669_, v___x_676_);
v_indexes_678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_664_, v_inst_665_, v_indexes_670_, v_key_667_, v_f_675_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 1, v_indexes_678_);
lean_ctor_set(v___x_672_, 0, v_entries_677_);
v___x_680_ = v___x_672_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_entries_677_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_indexes_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_map_689_, lean_object* v_key_690_, lean_object* v_value_691_){
_start:
{
lean_object* v_entries_692_; lean_object* v_indexes_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_entries_692_ = lean_ctor_get(v_map_689_, 0);
v_indexes_693_ = lean_ctor_get(v_map_689_, 1);
v_isSharedCheck_705_ = !lean_is_exclusive(v_map_689_);
if (v_isSharedCheck_705_ == 0)
{
v___x_695_ = v_map_689_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_indexes_693_);
lean_inc(v_entries_692_);
lean_dec(v_map_689_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_i_697_; lean_object* v_f_698_; lean_object* v___x_699_; lean_object* v_entries_700_; lean_object* v_indexes_701_; lean_object* v___x_703_; 
v_i_697_ = lean_array_get_size(v_entries_692_);
v_f_698_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_698_, 0, v_i_697_);
lean_inc(v_key_690_);
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v_key_690_);
lean_ctor_set(v___x_699_, 1, v_value_691_);
v_entries_700_ = lean_array_push(v_entries_692_, v___x_699_);
v_indexes_701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_685_, v_inst_686_, v_indexes_693_, v_key_690_, v_f_698_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_indexes_701_);
lean_ctor_set(v___x_695_, 0, v_entries_700_);
v___x_703_ = v___x_695_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_entries_700_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_indexes_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_x1_709_, lean_object* v_x2_710_){
_start:
{
lean_object* v_entries_711_; lean_object* v_indexes_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_724_; 
v_entries_711_ = lean_ctor_get(v_x1_709_, 0);
v_indexes_712_ = lean_ctor_get(v_x1_709_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_x1_709_);
if (v_isSharedCheck_724_ == 0)
{
v___x_714_ = v_x1_709_;
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_indexes_712_);
lean_inc(v_entries_711_);
lean_dec(v_x1_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_724_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_i_716_; lean_object* v_f_717_; lean_object* v___x_718_; lean_object* v_entries_719_; lean_object* v_indexes_720_; lean_object* v___x_722_; 
v_i_716_ = lean_array_get_size(v_entries_711_);
v_f_717_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_717_, 0, v_i_716_);
lean_inc(v_key_706_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_key_706_);
lean_ctor_set(v___x_718_, 1, v_x2_710_);
v_entries_719_ = lean_array_push(v_entries_711_, v___x_718_);
v_indexes_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_707_, v_inst_708_, v_indexes_712_, v_key_706_, v_f_717_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_indexes_720_);
lean_ctor_set(v___x_714_, 0, v_entries_719_);
v___x_722_ = v___x_714_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_entries_719_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_indexes_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_map_727_, lean_object* v_key_728_, lean_object* v_values_729_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_730_ = lean_unsigned_to_nat(0u);
v___x_731_ = lean_array_get_size(v_values_729_);
v___x_732_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_733_ = lean_nat_dec_lt(v___x_730_, v___x_731_);
if (v___x_733_ == 0)
{
lean_dec_ref(v_values_729_);
lean_dec(v_key_728_);
lean_dec_ref(v_inst_726_);
lean_dec_ref(v_inst_725_);
return v_map_727_;
}
else
{
lean_object* v___f_734_; uint8_t v___x_735_; 
v___f_734_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_734_, 0, v_key_728_);
lean_closure_set(v___f_734_, 1, v_inst_725_);
lean_closure_set(v___f_734_, 2, v_inst_726_);
v___x_735_ = lean_nat_dec_le(v___x_731_, v___x_731_);
if (v___x_735_ == 0)
{
if (v___x_733_ == 0)
{
lean_dec_ref(v___f_734_);
lean_dec_ref(v_values_729_);
return v_map_727_;
}
else
{
size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; 
v___x_736_ = ((size_t)0ULL);
v___x_737_ = lean_usize_of_nat(v___x_731_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_734_, v_values_729_, v___x_736_, v___x_737_, v_map_727_);
return v___x_738_;
}
}
else
{
size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_731_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_734_, v_values_729_, v___x_739_, v___x_740_, v_map_727_);
return v___x_741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_742_, lean_object* v_00_u03b2_743_, lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_map_748_, lean_object* v_key_749_, lean_object* v_values_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_array_get_size(v_values_750_);
v___x_753_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_754_ = lean_nat_dec_lt(v___x_751_, v___x_752_);
if (v___x_754_ == 0)
{
lean_dec_ref(v_values_750_);
lean_dec(v_key_749_);
lean_dec_ref(v_inst_745_);
lean_dec_ref(v_inst_744_);
return v_map_748_;
}
else
{
lean_object* v___f_755_; uint8_t v___x_756_; 
v___f_755_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_755_, 0, v_key_749_);
lean_closure_set(v___f_755_, 1, v_inst_744_);
lean_closure_set(v___f_755_, 2, v_inst_745_);
v___x_756_ = lean_nat_dec_le(v___x_752_, v___x_752_);
if (v___x_756_ == 0)
{
if (v___x_754_ == 0)
{
lean_dec_ref(v___f_755_);
lean_dec_ref(v_values_750_);
return v_map_748_;
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_752_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_753_, v___f_755_, v_values_750_, v___x_757_, v___x_758_, v_map_748_);
return v___x_759_;
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_752_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_753_, v___f_755_, v_values_750_, v___x_760_, v___x_761_, v_map_748_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_inst_765_, lean_object* v_inst_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_inst_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_768_, v_00_u03b2_769_, v_inst_770_, v_inst_771_);
lean_dec_ref(v_inst_771_);
lean_dec_ref(v_inst_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_acc_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_fst_777_; lean_object* v_entries_778_; lean_object* v_indexes_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_790_; 
v_fst_777_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_fst_777_);
v_entries_778_ = lean_ctor_get(v_acc_775_, 0);
v_indexes_779_ = lean_ctor_get(v_acc_775_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_acc_775_);
if (v_isSharedCheck_790_ == 0)
{
v___x_781_ = v_acc_775_;
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_indexes_779_);
lean_inc(v_entries_778_);
lean_dec(v_acc_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_i_783_; lean_object* v_f_784_; lean_object* v_entries_785_; lean_object* v_indexes_786_; lean_object* v___x_788_; 
v_i_783_ = lean_array_get_size(v_entries_778_);
v_f_784_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_784_, 0, v_i_783_);
v_entries_785_ = lean_array_push(v_entries_778_, v_x_776_);
v_indexes_786_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_773_, v_inst_774_, v_indexes_779_, v_fst_777_, v_f_784_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_indexes_786_);
lean_ctor_set(v___x_781_, 0, v_entries_785_);
v___x_788_ = v___x_781_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_entries_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_indexes_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_pairs_793_){
_start:
{
lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_inc_ref(v_inst_792_);
lean_inc_ref(v_inst_791_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_794_, 0, v_inst_791_);
lean_closure_set(v___f_794_, 1, v_inst_792_);
v___x_795_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_791_, v_inst_792_);
lean_dec_ref(v_inst_792_);
lean_dec_ref(v_inst_791_);
v___x_796_ = l_List_foldl___redArg(v___f_794_, v___x_795_, v_pairs_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_pairs_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_799_, v_inst_800_, v_pairs_803_);
return v___x_804_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_, lean_object* v_map_807_, lean_object* v_key_808_){
_start:
{
lean_object* v_indexes_809_; uint8_t v___x_810_; 
v_indexes_809_ = lean_ctor_get(v_map_807_, 1);
v___x_810_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_805_, v_inst_806_, v_indexes_809_, v_key_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_map_813_, lean_object* v_key_814_){
_start:
{
uint8_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_811_, v_inst_812_, v_map_813_, v_key_814_);
lean_dec_ref(v_map_813_);
v_r_816_ = lean_box(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_817_, lean_object* v_00_u03b2_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_map_821_, lean_object* v_key_822_){
_start:
{
lean_object* v_indexes_823_; uint8_t v___x_824_; 
v_indexes_823_ = lean_ctor_get(v_map_821_, 1);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_819_, v_inst_820_, v_indexes_823_, v_key_822_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_inst_827_, lean_object* v_inst_828_, lean_object* v_map_829_, lean_object* v_key_830_){
_start:
{
uint8_t v_res_831_; lean_object* v_r_832_; 
v_res_831_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_825_, v_00_u03b2_826_, v_inst_827_, v_inst_828_, v_map_829_, v_key_830_);
lean_dec_ref(v_map_829_);
v_r_832_ = lean_box(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_833_, lean_object* v_inst_834_, lean_object* v_key_835_, lean_object* v_f_836_, lean_object* v_x1_837_, lean_object* v_x2_838_){
_start:
{
lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_865_; 
v_fst_839_ = lean_ctor_get(v_x2_838_, 0);
v_snd_840_ = lean_ctor_get(v_x2_838_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x2_838_);
if (v_isSharedCheck_865_ == 0)
{
v___x_842_ = v_x2_838_;
v_isShared_843_ = v_isSharedCheck_865_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
lean_dec(v_x2_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_865_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___y_845_; lean_object* v___x_862_; uint8_t v___x_863_; 
lean_inc_ref(v_inst_833_);
lean_inc(v_fst_839_);
v___x_862_ = lean_apply_2(v_inst_833_, v_fst_839_, v_key_835_);
v___x_863_ = lean_unbox(v___x_862_);
if (v___x_863_ == 0)
{
lean_dec(v_f_836_);
v___y_845_ = v_snd_840_;
goto v___jp_844_;
}
else
{
lean_object* v___x_864_; 
v___x_864_ = lean_apply_1(v_f_836_, v_snd_840_);
v___y_845_ = v___x_864_;
goto v___jp_844_;
}
v___jp_844_:
{
lean_object* v_entries_846_; lean_object* v_indexes_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_861_; 
v_entries_846_ = lean_ctor_get(v_x1_837_, 0);
v_indexes_847_ = lean_ctor_get(v_x1_837_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v_x1_837_);
if (v_isSharedCheck_861_ == 0)
{
v___x_849_ = v_x1_837_;
v_isShared_850_ = v_isSharedCheck_861_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_indexes_847_);
lean_inc(v_entries_846_);
lean_dec(v_x1_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_861_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_i_851_; lean_object* v_f_852_; lean_object* v___x_854_; 
v_i_851_ = lean_array_get_size(v_entries_846_);
v_f_852_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_852_, 0, v_i_851_);
lean_inc(v_fst_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___y_845_);
v___x_854_ = v___x_842_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_839_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___y_845_);
v___x_854_ = v_reuseFailAlloc_860_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v_entries_855_; lean_object* v_indexes_856_; lean_object* v___x_858_; 
v_entries_855_ = lean_array_push(v_entries_846_, v___x_854_);
v_indexes_856_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_833_, v_inst_834_, v_indexes_847_, v_fst_839_, v_f_852_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v_indexes_856_);
lean_ctor_set(v___x_849_, 0, v_entries_855_);
v___x_858_ = v___x_849_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_entries_855_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_indexes_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_map_868_, lean_object* v_key_869_, lean_object* v_f_870_){
_start:
{
uint8_t v___x_871_; 
lean_inc(v_key_869_);
lean_inc_ref(v_inst_867_);
lean_inc_ref(v_inst_866_);
v___x_871_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_866_, v_inst_867_, v_key_869_, v_map_868_);
if (v___x_871_ == 0)
{
lean_dec(v_f_870_);
lean_dec(v_key_869_);
lean_dec_ref(v_inst_867_);
lean_dec_ref(v_inst_866_);
return v_map_868_;
}
else
{
lean_object* v_entries_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_entries_872_ = lean_ctor_get(v_map_868_, 0);
lean_inc_ref(v_entries_872_);
lean_dec_ref(v_map_868_);
v___x_873_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_866_, v_inst_867_);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_array_get_size(v_entries_872_);
v___x_876_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_877_ = lean_nat_dec_lt(v___x_874_, v___x_875_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_entries_872_);
lean_dec(v_f_870_);
lean_dec(v_key_869_);
lean_dec_ref(v_inst_867_);
lean_dec_ref(v_inst_866_);
return v___x_873_;
}
else
{
lean_object* v___f_878_; uint8_t v___x_879_; 
v___f_878_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_878_, 0, v_inst_866_);
lean_closure_set(v___f_878_, 1, v_inst_867_);
lean_closure_set(v___f_878_, 2, v_key_869_);
lean_closure_set(v___f_878_, 3, v_f_870_);
v___x_879_ = lean_nat_dec_le(v___x_875_, v___x_875_);
if (v___x_879_ == 0)
{
if (v___x_877_ == 0)
{
lean_dec_ref(v___f_878_);
lean_dec_ref(v_entries_872_);
return v___x_873_;
}
else
{
size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; 
v___x_880_ = ((size_t)0ULL);
v___x_881_ = lean_usize_of_nat(v___x_875_);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_876_, v___f_878_, v_entries_872_, v___x_880_, v___x_881_, v___x_873_);
return v___x_882_;
}
}
else
{
size_t v___x_883_; size_t v___x_884_; lean_object* v___x_885_; 
v___x_883_ = ((size_t)0ULL);
v___x_884_ = lean_usize_of_nat(v___x_875_);
v___x_885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_876_, v___f_878_, v_entries_872_, v___x_883_, v___x_884_, v___x_873_);
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_map_892_, lean_object* v_key_893_, lean_object* v_f_894_){
_start:
{
uint8_t v___x_895_; 
lean_inc(v_key_893_);
lean_inc_ref(v_inst_889_);
lean_inc_ref(v_inst_888_);
v___x_895_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_888_, v_inst_889_, v_key_893_, v_map_892_);
if (v___x_895_ == 0)
{
lean_dec(v_f_894_);
lean_dec(v_key_893_);
lean_dec_ref(v_inst_889_);
lean_dec_ref(v_inst_888_);
return v_map_892_;
}
else
{
lean_object* v_entries_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v_entries_896_ = lean_ctor_get(v_map_892_, 0);
lean_inc_ref(v_entries_896_);
lean_dec_ref(v_map_892_);
v___x_897_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_888_, v_inst_889_);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_array_get_size(v_entries_896_);
v___x_900_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_901_ = lean_nat_dec_lt(v___x_898_, v___x_899_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_entries_896_);
lean_dec(v_f_894_);
lean_dec(v_key_893_);
lean_dec_ref(v_inst_889_);
lean_dec_ref(v_inst_888_);
return v___x_897_;
}
else
{
lean_object* v___f_902_; uint8_t v___x_903_; 
v___f_902_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_902_, 0, v_inst_888_);
lean_closure_set(v___f_902_, 1, v_inst_889_);
lean_closure_set(v___f_902_, 2, v_key_893_);
lean_closure_set(v___f_902_, 3, v_f_894_);
v___x_903_ = lean_nat_dec_le(v___x_899_, v___x_899_);
if (v___x_903_ == 0)
{
if (v___x_901_ == 0)
{
lean_dec_ref(v___f_902_);
lean_dec_ref(v_entries_896_);
return v___x_897_;
}
else
{
size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((size_t)0ULL);
v___x_905_ = lean_usize_of_nat(v___x_899_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_900_, v___f_902_, v_entries_896_, v___x_904_, v___x_905_, v___x_897_);
return v___x_906_;
}
}
else
{
size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((size_t)0ULL);
v___x_908_ = lean_usize_of_nat(v___x_899_);
v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_900_, v___f_902_, v_entries_896_, v___x_907_, v___x_908_, v___x_897_);
return v___x_909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_910_, lean_object* v_inst_911_, lean_object* v_map_912_, lean_object* v_key_913_, lean_object* v_value_914_){
_start:
{
uint8_t v___x_915_; 
lean_inc(v_key_913_);
lean_inc_ref(v_inst_911_);
lean_inc_ref(v_inst_910_);
v___x_915_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_910_, v_inst_911_, v_key_913_, v_map_912_);
if (v___x_915_ == 0)
{
lean_dec(v_value_914_);
lean_dec(v_key_913_);
lean_dec_ref(v_inst_911_);
lean_dec_ref(v_inst_910_);
return v_map_912_;
}
else
{
lean_object* v_entries_916_; lean_object* v_indexes_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_931_; 
v_entries_916_ = lean_ctor_get(v_map_912_, 0);
v_indexes_917_ = lean_ctor_get(v_map_912_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_map_912_);
if (v_isSharedCheck_931_ == 0)
{
v___x_919_ = v_map_912_;
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_indexes_917_);
lean_inc(v_entries_916_);
lean_dec(v_map_912_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_931_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_idxs_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v_lastIdx_925_; lean_object* v___x_926_; lean_object* v_entries_927_; lean_object* v___x_929_; 
lean_inc(v_key_913_);
v_idxs_921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_910_, v_inst_911_, v_indexes_917_, v_key_913_);
v___x_922_ = lean_array_get_size(v_idxs_921_);
v___x_923_ = lean_unsigned_to_nat(1u);
v___x_924_ = lean_nat_sub(v___x_922_, v___x_923_);
v_lastIdx_925_ = lean_array_fget(v_idxs_921_, v___x_924_);
lean_dec(v___x_924_);
lean_dec(v_idxs_921_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_key_913_);
lean_ctor_set(v___x_926_, 1, v_value_914_);
v_entries_927_ = lean_array_fset(v_entries_916_, v_lastIdx_925_, v___x_926_);
lean_dec(v_lastIdx_925_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_entries_927_);
v___x_929_ = v___x_919_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_entries_927_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_indexes_917_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_932_, lean_object* v_00_u03b2_933_, lean_object* v_inst_934_, lean_object* v_inst_935_, lean_object* v_map_936_, lean_object* v_key_937_, lean_object* v_value_938_){
_start:
{
uint8_t v___x_939_; 
lean_inc(v_key_937_);
lean_inc_ref(v_inst_935_);
lean_inc_ref(v_inst_934_);
v___x_939_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_934_, v_inst_935_, v_key_937_, v_map_936_);
if (v___x_939_ == 0)
{
lean_dec(v_value_938_);
lean_dec(v_key_937_);
lean_dec_ref(v_inst_935_);
lean_dec_ref(v_inst_934_);
return v_map_936_;
}
else
{
lean_object* v_entries_940_; lean_object* v_indexes_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_955_; 
v_entries_940_ = lean_ctor_get(v_map_936_, 0);
v_indexes_941_ = lean_ctor_get(v_map_936_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_map_936_);
if (v_isSharedCheck_955_ == 0)
{
v___x_943_ = v_map_936_;
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_indexes_941_);
lean_inc(v_entries_940_);
lean_dec(v_map_936_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_idxs_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_lastIdx_949_; lean_object* v___x_950_; lean_object* v_entries_951_; lean_object* v___x_953_; 
lean_inc(v_key_937_);
v_idxs_945_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_934_, v_inst_935_, v_indexes_941_, v_key_937_);
v___x_946_ = lean_array_get_size(v_idxs_945_);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_nat_sub(v___x_946_, v___x_947_);
v_lastIdx_949_ = lean_array_fget(v_idxs_945_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v_idxs_945_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_key_937_);
lean_ctor_set(v___x_950_, 1, v_value_938_);
v_entries_951_ = lean_array_fset(v_entries_940_, v_lastIdx_949_, v___x_950_);
lean_dec(v_lastIdx_949_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v_entries_951_);
v___x_953_ = v___x_943_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_entries_951_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_indexes_941_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_x1_958_, lean_object* v_x2_959_){
_start:
{
lean_object* v_fst_960_; lean_object* v_entries_961_; lean_object* v_indexes_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_fst_960_ = lean_ctor_get(v_x2_959_, 0);
lean_inc(v_fst_960_);
v_entries_961_ = lean_ctor_get(v_x1_958_, 0);
v_indexes_962_ = lean_ctor_get(v_x1_958_, 1);
v_isSharedCheck_973_ = !lean_is_exclusive(v_x1_958_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v_x1_958_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_indexes_962_);
lean_inc(v_entries_961_);
lean_dec(v_x1_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_i_966_; lean_object* v_f_967_; lean_object* v_entries_968_; lean_object* v_indexes_969_; lean_object* v___x_971_; 
v_i_966_ = lean_array_get_size(v_entries_961_);
v_f_967_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_967_, 0, v_i_966_);
v_entries_968_ = lean_array_push(v_entries_961_, v_x2_959_);
v_indexes_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_956_, v_inst_957_, v_indexes_962_, v_fst_960_, v_f_967_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_indexes_969_);
lean_ctor_set(v___x_964_, 0, v_entries_968_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_entries_968_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v_indexes_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object* v_inst_974_, lean_object* v_key_975_, lean_object* v_x1_976_, lean_object* v_x2_977_){
_start:
{
lean_object* v_fst_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_fst_978_ = lean_ctor_get(v_x2_977_, 0);
lean_inc(v_fst_978_);
v___x_979_ = lean_apply_2(v_inst_974_, v_fst_978_, v_key_975_);
v___x_980_ = lean_unbox(v___x_979_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_array_push(v_x1_976_, v_x2_977_);
return v___x_981_;
}
else
{
lean_dec_ref(v_x2_977_);
return v_x1_976_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_map_984_, lean_object* v_key_985_){
_start:
{
uint8_t v___x_986_; 
lean_inc(v_key_985_);
lean_inc_ref(v_inst_983_);
lean_inc_ref(v_inst_982_);
v___x_986_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_982_, v_inst_983_, v_key_985_, v_map_984_);
if (v___x_986_ == 0)
{
lean_dec(v_key_985_);
lean_dec_ref(v_inst_983_);
lean_dec_ref(v_inst_982_);
return v_map_984_;
}
else
{
lean_object* v_entries_987_; lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___y_992_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_entries_987_ = lean_ctor_get(v_map_984_, 0);
lean_inc_ref(v_entries_987_);
lean_dec_ref(v_map_984_);
lean_inc_ref(v_inst_983_);
lean_inc_ref(v_inst_982_);
v___f_988_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_988_, 0, v_inst_982_);
lean_closure_set(v___f_988_, 1, v_inst_983_);
v___x_989_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_982_, v_inst_983_);
lean_dec_ref(v_inst_983_);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_entries_987_);
v___x_1004_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1005_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1006_ = lean_nat_dec_lt(v___x_990_, v___x_1003_);
if (v___x_1006_ == 0)
{
lean_dec_ref(v_entries_987_);
lean_dec(v_key_985_);
lean_dec_ref(v_inst_982_);
v___y_992_ = v___x_1004_;
goto v___jp_991_;
}
else
{
lean_object* v___f_1007_; uint8_t v___x_1008_; 
v___f_1007_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1007_, 0, v_inst_982_);
lean_closure_set(v___f_1007_, 1, v_key_985_);
v___x_1008_ = lean_nat_dec_le(v___x_1003_, v___x_1003_);
if (v___x_1008_ == 0)
{
if (v___x_1006_ == 0)
{
lean_dec_ref(v___f_1007_);
lean_dec_ref(v_entries_987_);
v___y_992_ = v___x_1004_;
goto v___jp_991_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = lean_usize_of_nat(v___x_1003_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1005_, v___f_1007_, v_entries_987_, v___x_1009_, v___x_1010_, v___x_1004_);
v___y_992_ = v___x_1011_;
goto v___jp_991_;
}
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1003_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1005_, v___f_1007_, v_entries_987_, v___x_1012_, v___x_1013_, v___x_1004_);
v___y_992_ = v___x_1014_;
goto v___jp_991_;
}
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_993_ = lean_array_get_size(v___y_992_);
v___x_994_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_995_ = lean_nat_dec_lt(v___x_990_, v___x_993_);
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_992_);
lean_dec_ref(v___f_988_);
return v___x_989_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_996_ == 0)
{
if (v___x_995_ == 0)
{
lean_dec_ref(v___y_992_);
lean_dec_ref(v___f_988_);
return v___x_989_;
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((size_t)0ULL);
v___x_998_ = lean_usize_of_nat(v___x_993_);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_994_, v___f_988_, v___y_992_, v___x_997_, v___x_998_, v___x_989_);
return v___x_999_;
}
}
else
{
size_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = lean_usize_of_nat(v___x_993_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_994_, v___f_988_, v___y_992_, v___x_1000_, v___x_1001_, v___x_989_);
return v___x_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_map_1021_, lean_object* v_key_1022_){
_start:
{
uint8_t v___x_1023_; 
lean_inc(v_key_1022_);
lean_inc_ref(v_inst_1018_);
lean_inc_ref(v_inst_1017_);
v___x_1023_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1017_, v_inst_1018_, v_key_1022_, v_map_1021_);
if (v___x_1023_ == 0)
{
lean_dec(v_key_1022_);
lean_dec_ref(v_inst_1018_);
lean_dec_ref(v_inst_1017_);
return v_map_1021_;
}
else
{
lean_object* v_entries_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___y_1029_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_entries_1024_ = lean_ctor_get(v_map_1021_, 0);
lean_inc_ref(v_entries_1024_);
lean_dec_ref(v_map_1021_);
lean_inc_ref(v_inst_1018_);
lean_inc_ref(v_inst_1017_);
v___f_1025_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1025_, 0, v_inst_1017_);
lean_closure_set(v___f_1025_, 1, v_inst_1018_);
v___x_1026_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1017_, v_inst_1018_);
lean_dec_ref(v_inst_1018_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v_entries_1024_);
v___x_1041_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1042_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1043_ = lean_nat_dec_lt(v___x_1027_, v___x_1040_);
if (v___x_1043_ == 0)
{
lean_dec_ref(v_entries_1024_);
lean_dec(v_key_1022_);
lean_dec_ref(v_inst_1017_);
v___y_1029_ = v___x_1041_;
goto v___jp_1028_;
}
else
{
lean_object* v___f_1044_; uint8_t v___x_1045_; 
v___f_1044_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1044_, 0, v_inst_1017_);
lean_closure_set(v___f_1044_, 1, v_key_1022_);
v___x_1045_ = lean_nat_dec_le(v___x_1040_, v___x_1040_);
if (v___x_1045_ == 0)
{
if (v___x_1043_ == 0)
{
lean_dec_ref(v___f_1044_);
lean_dec_ref(v_entries_1024_);
v___y_1029_ = v___x_1041_;
goto v___jp_1028_;
}
else
{
size_t v___x_1046_; size_t v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = lean_usize_of_nat(v___x_1040_);
v___x_1048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1042_, v___f_1044_, v_entries_1024_, v___x_1046_, v___x_1047_, v___x_1041_);
v___y_1029_ = v___x_1048_;
goto v___jp_1028_;
}
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = lean_usize_of_nat(v___x_1040_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1042_, v___f_1044_, v_entries_1024_, v___x_1049_, v___x_1050_, v___x_1041_);
v___y_1029_ = v___x_1051_;
goto v___jp_1028_;
}
}
v___jp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1030_ = lean_array_get_size(v___y_1029_);
v___x_1031_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1032_ = lean_nat_dec_lt(v___x_1027_, v___x_1030_);
if (v___x_1032_ == 0)
{
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___f_1025_);
return v___x_1026_;
}
else
{
uint8_t v___x_1033_; 
v___x_1033_ = lean_nat_dec_le(v___x_1030_, v___x_1030_);
if (v___x_1033_ == 0)
{
if (v___x_1032_ == 0)
{
lean_dec_ref(v___y_1029_);
lean_dec_ref(v___f_1025_);
return v___x_1026_;
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = lean_usize_of_nat(v___x_1030_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1031_, v___f_1025_, v___y_1029_, v___x_1034_, v___x_1035_, v___x_1026_);
return v___x_1036_;
}
}
else
{
size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = lean_usize_of_nat(v___x_1030_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1031_, v___f_1025_, v___y_1029_, v___x_1037_, v___x_1038_, v___x_1026_);
return v___x_1039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1052_){
_start:
{
lean_object* v_entries_1053_; lean_object* v___x_1054_; 
v_entries_1053_ = lean_ctor_get(v_map_1052_, 0);
v___x_1054_ = lean_array_get_size(v_entries_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1055_);
lean_dec_ref(v_map_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_map_1061_){
_start:
{
lean_object* v_entries_1062_; lean_object* v___x_1063_; 
v_entries_1062_ = lean_ctor_get(v_map_1061_, 0);
v___x_1063_ = lean_array_get_size(v_entries_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_map_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1064_, v_00_u03b2_1065_, v_inst_1066_, v_inst_1067_, v_map_1068_);
lean_dec_ref(v_map_1068_);
lean_dec_ref(v_inst_1067_);
lean_dec_ref(v_inst_1066_);
return v_res_1069_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1070_){
_start:
{
lean_object* v_entries_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_entries_1071_ = lean_ctor_get(v_map_1070_, 0);
v___x_1072_ = lean_array_get_size(v_entries_1071_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v___x_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1075_);
lean_dec_ref(v_map_1075_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_map_1082_){
_start:
{
lean_object* v_entries_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_entries_1083_ = lean_ctor_get(v_map_1082_, 0);
v___x_1084_ = lean_array_get_size(v_entries_1083_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_nat_dec_eq(v___x_1084_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_map_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1087_, v_00_u03b2_1088_, v_inst_1089_, v_inst_1090_, v_map_1091_);
lean_dec_ref(v_map_1091_);
lean_dec_ref(v_inst_1090_);
lean_dec_ref(v_inst_1089_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1094_){
_start:
{
lean_object* v_entries_1095_; 
v_entries_1095_ = lean_ctor_get(v_map_1094_, 0);
lean_inc_ref(v_entries_1095_);
return v_entries_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1096_);
lean_dec_ref(v_map_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_map_1102_){
_start:
{
lean_object* v_entries_1103_; 
v_entries_1103_ = lean_ctor_get(v_map_1102_, 0);
lean_inc_ref(v_entries_1103_);
return v_entries_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_map_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1104_, v_00_u03b2_1105_, v_inst_1106_, v_inst_1107_, v_map_1108_);
lean_dec_ref(v_map_1108_);
lean_dec_ref(v_inst_1107_);
lean_dec_ref(v_inst_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1110_){
_start:
{
lean_object* v_entries_1111_; lean_object* v___x_1112_; 
v_entries_1111_ = lean_ctor_get(v_map_1110_, 0);
lean_inc_ref(v_entries_1111_);
lean_dec_ref(v_map_1110_);
v___x_1112_ = lean_array_to_list(v_entries_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_map_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_map_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1119_, v_00_u03b2_1120_, v_inst_1121_, v_inst_1122_, v_map_1123_);
lean_dec_ref(v_inst_1122_);
lean_dec_ref(v_inst_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_m1_1127_, lean_object* v_m2_1128_){
_start:
{
lean_object* v_entries_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_entries_1129_ = lean_ctor_get(v_m2_1128_, 0);
lean_inc_ref(v_entries_1129_);
lean_dec_ref(v_m2_1128_);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_entries_1129_);
v___x_1132_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1133_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1133_ == 0)
{
lean_dec_ref(v_entries_1129_);
lean_dec_ref(v_inst_1126_);
lean_dec_ref(v_inst_1125_);
return v_m1_1127_;
}
else
{
lean_object* v___f_1134_; uint8_t v___x_1135_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1134_, 0, v_inst_1125_);
lean_closure_set(v___f_1134_, 1, v_inst_1126_);
v___x_1135_ = lean_nat_dec_le(v___x_1131_, v___x_1131_);
if (v___x_1135_ == 0)
{
if (v___x_1133_ == 0)
{
lean_dec_ref(v___f_1134_);
lean_dec_ref(v_entries_1129_);
return v_m1_1127_;
}
else
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = lean_usize_of_nat(v___x_1131_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1134_, v_entries_1129_, v___x_1136_, v___x_1137_, v_m1_1127_);
return v___x_1138_;
}
}
else
{
size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = lean_usize_of_nat(v___x_1131_);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v___f_1134_, v_entries_1129_, v___x_1139_, v___x_1140_, v_m1_1127_);
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_m1_1148_, lean_object* v_m2_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1144_, v_inst_1145_, v_m1_1148_, v_m2_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object* v_inst_1151_, lean_object* v_inst_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1151_, v_inst_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v_inst_1154_, lean_object* v_inst_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_1154_, v_inst_1155_);
lean_dec_ref(v_inst_1155_);
lean_dec_ref(v_inst_1154_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1159_, v_inst_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1162_, v_00_u03b2_1163_, v_inst_1164_, v_inst_1165_);
lean_dec_ref(v_inst_1165_);
lean_dec_ref(v_inst_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_x_1169_){
_start:
{
lean_object* v_fst_1170_; lean_object* v___x_1171_; lean_object* v_entries_1172_; lean_object* v_indexes_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1184_; 
v_fst_1170_ = lean_ctor_get(v_x_1169_, 0);
lean_inc(v_fst_1170_);
v___x_1171_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1167_, v_inst_1168_);
v_entries_1172_ = lean_ctor_get(v___x_1171_, 0);
v_indexes_1173_ = lean_ctor_get(v___x_1171_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1175_ = v___x_1171_;
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_indexes_1173_);
lean_inc(v_entries_1172_);
lean_dec(v___x_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_i_1177_; lean_object* v_f_1178_; lean_object* v_entries_1179_; lean_object* v_indexes_1180_; lean_object* v___x_1182_; 
v_i_1177_ = lean_array_get_size(v_entries_1172_);
v_f_1178_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1178_, 0, v_i_1177_);
v_entries_1179_ = lean_array_push(v_entries_1172_, v_x_1169_);
v_indexes_1180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1167_, v_inst_1168_, v_indexes_1173_, v_fst_1170_, v_f_1178_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_indexes_1180_);
lean_ctor_set(v___x_1175_, 0, v_entries_1179_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_entries_1179_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_indexes_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1185_, lean_object* v_inst_1186_){
_start:
{
lean_object* v___f_1187_; 
v___f_1187_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1187_, 0, v_inst_1185_);
lean_closure_set(v___f_1187_, 1, v_inst_1186_);
return v___f_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1188_, lean_object* v_00_u03b2_1189_, lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_){
_start:
{
lean_object* v___f_1194_; 
v___f_1194_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1194_, 0, v_inst_1190_);
lean_closure_set(v___f_1194_, 1, v_inst_1191_);
return v___f_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_x_1197_, lean_object* v_m_1198_){
_start:
{
lean_object* v_fst_1199_; lean_object* v_entries_1200_; lean_object* v_indexes_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1212_; 
v_fst_1199_ = lean_ctor_get(v_x_1197_, 0);
lean_inc(v_fst_1199_);
v_entries_1200_ = lean_ctor_get(v_m_1198_, 0);
v_indexes_1201_ = lean_ctor_get(v_m_1198_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_m_1198_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1203_ = v_m_1198_;
v_isShared_1204_ = v_isSharedCheck_1212_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_indexes_1201_);
lean_inc(v_entries_1200_);
lean_dec(v_m_1198_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1212_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_i_1205_; lean_object* v_f_1206_; lean_object* v_entries_1207_; lean_object* v_indexes_1208_; lean_object* v___x_1210_; 
v_i_1205_ = lean_array_get_size(v_entries_1200_);
v_f_1206_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1206_, 0, v_i_1205_);
v_entries_1207_ = lean_array_push(v_entries_1200_, v_x_1197_);
v_indexes_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1195_, v_inst_1196_, v_indexes_1201_, v_fst_1199_, v_f_1206_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v_indexes_1208_);
lean_ctor_set(v___x_1203_, 0, v_entries_1207_);
v___x_1210_ = v___x_1203_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_entries_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_indexes_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v___f_1215_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1215_, 0, v_inst_1213_);
lean_closure_set(v___f_1215_, 1, v_inst_1214_);
return v___f_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___f_1222_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1222_, 0, v_inst_1218_);
lean_closure_set(v___f_1222_, 1, v_inst_1219_);
return v___f_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1225_, 0, lean_box(0));
lean_closure_set(v___x_1225_, 1, lean_box(0));
lean_closure_set(v___x_1225_, 2, v_inst_1223_);
lean_closure_set(v___x_1225_, 3, v_inst_1224_);
lean_closure_set(v___x_1225_, 4, lean_box(0));
lean_closure_set(v___x_1225_, 5, lean_box(0));
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1232_, 0, lean_box(0));
lean_closure_set(v___x_1232_, 1, lean_box(0));
lean_closure_set(v___x_1232_, 2, v_inst_1228_);
lean_closure_set(v___x_1232_, 3, v_inst_1229_);
lean_closure_set(v___x_1232_, 4, lean_box(0));
lean_closure_set(v___x_1232_, 5, lean_box(0));
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1233_, lean_object* v_a_1234_, lean_object* v_x_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_apply_2(v_f_1233_, v_a_1234_, v___y_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_map_1240_, lean_object* v_b_1241_, lean_object* v_f_1242_){
_start:
{
lean_object* v_entries_1243_; lean_object* v___f_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v_entries_1243_ = lean_ctor_get(v_map_1240_, 0);
lean_inc_ref(v_entries_1243_);
lean_dec_ref(v_map_1240_);
v___f_1244_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1244_, 0, v_f_1242_);
v_sz_1245_ = lean_array_size(v_entries_1243_);
v___x_1246_ = ((size_t)0ULL);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v_entries_1243_, v___f_1244_, v_sz_1245_, v___x_1246_, v_b_1241_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1248_){
_start:
{
lean_object* v___f_1249_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1249_, 0, v_inst_1248_);
return v___f_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_m_1254_, lean_object* v_inst_1255_){
_start:
{
lean_object* v___f_1256_; 
v___f_1256_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1256_, 0, v_inst_1255_);
return v___f_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_m_1261_, lean_object* v_inst_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1257_, v_00_u03b2_1258_, v_inst_1259_, v_inst_1260_, v_m_1261_, v_inst_1262_);
lean_dec_ref(v_inst_1260_);
lean_dec_ref(v_inst_1259_);
return v_res_1263_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_IndexMultiMap(builtin);
}
#ifdef __cplusplus
}
#endif
