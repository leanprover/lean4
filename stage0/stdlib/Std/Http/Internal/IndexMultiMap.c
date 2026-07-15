// Lean compiler output
// Module: Std.Http.Internal.IndexMultiMap
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
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_entries_258_; lean_object* v_indexes_259_; lean_object* v___x_260_; lean_object* v___f_261_; lean_object* v___x_262_; size_t v_sz_263_; size_t v___x_264_; lean_object* v_entries_265_; 
v_entries_258_ = lean_ctor_get(v_map_256_, 0);
lean_inc_ref(v_entries_258_);
v_indexes_259_ = lean_ctor_get(v_map_256_, 1);
lean_inc_ref(v_indexes_259_);
lean_dec_ref(v_map_256_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_254_, v_inst_255_, v_indexes_259_, v_key_257_);
lean_dec_ref(v_indexes_259_);
lean_inc_n(v___x_260_, 2);
v___f_261_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_261_, 0, v___x_260_);
lean_closure_set(v___f_261_, 1, v_entries_258_);
v___x_262_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_263_ = lean_array_size(v___x_260_);
v___x_264_ = ((size_t)0ULL);
v_entries_265_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_262_, v___x_260_, v___f_261_, v_sz_263_, v___x_264_, v___x_260_);
lean_dec(v___x_260_);
return v_entries_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_map_270_, lean_object* v_key_271_, lean_object* v_h_272_){
_start:
{
lean_object* v_entries_273_; lean_object* v_indexes_274_; lean_object* v___x_275_; lean_object* v___f_276_; lean_object* v___x_277_; size_t v_sz_278_; size_t v___x_279_; lean_object* v_entries_280_; 
v_entries_273_ = lean_ctor_get(v_map_270_, 0);
lean_inc_ref(v_entries_273_);
v_indexes_274_ = lean_ctor_get(v_map_270_, 1);
lean_inc_ref(v_indexes_274_);
lean_dec_ref(v_map_270_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_268_, v_inst_269_, v_indexes_274_, v_key_271_);
lean_dec_ref(v_indexes_274_);
lean_inc_n(v___x_275_, 2);
v___f_276_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_276_, 0, v___x_275_);
lean_closure_set(v___f_276_, 1, v_entries_273_);
v___x_277_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_278_ = lean_array_size(v___x_275_);
v___x_279_ = ((size_t)0ULL);
v_entries_280_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_277_, v___x_275_, v___f_276_, v_sz_278_, v___x_279_, v___x_275_);
lean_dec(v___x_275_);
return v_entries_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_map_283_, lean_object* v_key_284_){
_start:
{
lean_object* v_entries_285_; lean_object* v_indexes_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v_entry_289_; lean_object* v___x_290_; lean_object* v_snd_291_; 
v_entries_285_ = lean_ctor_get(v_map_283_, 0);
v_indexes_286_ = lean_ctor_get(v_map_283_, 1);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_281_, v_inst_282_, v_indexes_286_, v_key_284_);
v___x_288_ = lean_unsigned_to_nat(0u);
v_entry_289_ = lean_array_fget(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_array_fget_borrowed(v_entries_285_, v_entry_289_);
lean_dec(v_entry_289_);
v_snd_291_ = lean_ctor_get(v___x_290_, 1);
lean_inc(v_snd_291_);
return v_snd_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_map_294_, lean_object* v_key_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_292_, v_inst_293_, v_map_294_, v_key_295_);
lean_dec_ref(v_map_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_map_301_, lean_object* v_key_302_, lean_object* v_h_303_){
_start:
{
lean_object* v_entries_304_; lean_object* v_indexes_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_entry_308_; lean_object* v___x_309_; lean_object* v_snd_310_; 
v_entries_304_ = lean_ctor_get(v_map_301_, 0);
v_indexes_305_ = lean_ctor_get(v_map_301_, 1);
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_299_, v_inst_300_, v_indexes_305_, v_key_302_);
v___x_307_ = lean_unsigned_to_nat(0u);
v_entry_308_ = lean_array_fget(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_array_fget_borrowed(v_entries_304_, v_entry_308_);
lean_dec(v_entry_308_);
v_snd_310_ = lean_ctor_get(v___x_309_, 1);
lean_inc(v_snd_310_);
return v_snd_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_311_, lean_object* v_00_u03b2_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_map_315_, lean_object* v_key_316_, lean_object* v_h_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_311_, v_00_u03b2_312_, v_inst_313_, v_inst_314_, v_map_315_, v_key_316_, v_h_317_);
lean_dec_ref(v_map_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_map_321_, lean_object* v_key_322_){
_start:
{
uint8_t v___x_323_; 
lean_inc(v_key_322_);
lean_inc_ref(v_inst_320_);
lean_inc_ref(v_inst_319_);
v___x_323_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_319_, v_inst_320_, v_key_322_, v_map_321_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v_key_322_);
lean_dec_ref(v_map_321_);
lean_dec_ref(v_inst_320_);
lean_dec_ref(v_inst_319_);
v___x_324_ = lean_box(0);
return v___x_324_;
}
else
{
lean_object* v_entries_325_; lean_object* v_indexes_326_; lean_object* v___x_327_; lean_object* v___f_328_; lean_object* v___x_329_; size_t v_sz_330_; size_t v___x_331_; lean_object* v_entries_332_; lean_object* v___x_333_; 
v_entries_325_ = lean_ctor_get(v_map_321_, 0);
lean_inc_ref(v_entries_325_);
v_indexes_326_ = lean_ctor_get(v_map_321_, 1);
lean_inc_ref(v_indexes_326_);
lean_dec_ref(v_map_321_);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_319_, v_inst_320_, v_indexes_326_, v_key_322_);
lean_dec_ref(v_indexes_326_);
lean_inc_n(v___x_327_, 2);
v___f_328_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_328_, 0, v___x_327_);
lean_closure_set(v___f_328_, 1, v_entries_325_);
v___x_329_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_330_ = lean_array_size(v___x_327_);
v___x_331_ = ((size_t)0ULL);
v_entries_332_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_329_, v___x_327_, v___f_328_, v_sz_330_, v___x_331_, v___x_327_);
lean_dec(v___x_327_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v_entries_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_334_, lean_object* v_00_u03b2_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_map_338_, lean_object* v_key_339_){
_start:
{
uint8_t v___x_340_; 
lean_inc(v_key_339_);
lean_inc_ref(v_inst_337_);
lean_inc_ref(v_inst_336_);
v___x_340_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_336_, v_inst_337_, v_key_339_, v_map_338_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_dec(v_key_339_);
lean_dec_ref(v_map_338_);
lean_dec_ref(v_inst_337_);
lean_dec_ref(v_inst_336_);
v___x_341_ = lean_box(0);
return v___x_341_;
}
else
{
lean_object* v_entries_342_; lean_object* v_indexes_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; size_t v_sz_347_; size_t v___x_348_; lean_object* v_entries_349_; lean_object* v___x_350_; 
v_entries_342_ = lean_ctor_get(v_map_338_, 0);
lean_inc_ref(v_entries_342_);
v_indexes_343_ = lean_ctor_get(v_map_338_, 1);
lean_inc_ref(v_indexes_343_);
lean_dec_ref(v_map_338_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_336_, v_inst_337_, v_indexes_343_, v_key_339_);
lean_dec_ref(v_indexes_343_);
lean_inc_n(v___x_344_, 2);
v___f_345_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_345_, 0, v___x_344_);
lean_closure_set(v___f_345_, 1, v_entries_342_);
v___x_346_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_347_ = lean_array_size(v___x_344_);
v___x_348_ = ((size_t)0ULL);
v_entries_349_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_346_, v___x_344_, v___f_345_, v_sz_347_, v___x_348_, v___x_344_);
lean_dec(v___x_344_);
v___x_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_350_, 0, v_entries_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_map_353_, lean_object* v_key_354_){
_start:
{
uint8_t v___x_355_; 
lean_inc(v_key_354_);
lean_inc_ref(v_inst_352_);
lean_inc_ref(v_inst_351_);
v___x_355_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_351_, v_inst_352_, v_key_354_, v_map_353_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v_key_354_);
lean_dec_ref(v_inst_352_);
lean_dec_ref(v_inst_351_);
v___x_356_ = lean_box(0);
return v___x_356_;
}
else
{
lean_object* v_entries_357_; lean_object* v_indexes_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_entry_361_; lean_object* v___x_362_; lean_object* v_snd_363_; lean_object* v___x_364_; 
v_entries_357_ = lean_ctor_get(v_map_353_, 0);
v_indexes_358_ = lean_ctor_get(v_map_353_, 1);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_351_, v_inst_352_, v_indexes_358_, v_key_354_);
v___x_360_ = lean_unsigned_to_nat(0u);
v_entry_361_ = lean_array_fget(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_array_fget_borrowed(v_entries_357_, v_entry_361_);
lean_dec(v_entry_361_);
v_snd_363_ = lean_ctor_get(v___x_362_, 1);
lean_inc(v_snd_363_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_snd_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_map_367_, lean_object* v_key_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_365_, v_inst_366_, v_map_367_, v_key_368_);
lean_dec_ref(v_map_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_map_374_, lean_object* v_key_375_){
_start:
{
uint8_t v___x_376_; 
lean_inc(v_key_375_);
lean_inc_ref(v_inst_373_);
lean_inc_ref(v_inst_372_);
v___x_376_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_372_, v_inst_373_, v_key_375_, v_map_374_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v_key_375_);
lean_dec_ref(v_inst_373_);
lean_dec_ref(v_inst_372_);
v___x_377_ = lean_box(0);
return v___x_377_;
}
else
{
lean_object* v_entries_378_; lean_object* v_indexes_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_entry_382_; lean_object* v___x_383_; lean_object* v_snd_384_; lean_object* v___x_385_; 
v_entries_378_ = lean_ctor_get(v_map_374_, 0);
v_indexes_379_ = lean_ctor_get(v_map_374_, 1);
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_372_, v_inst_373_, v_indexes_379_, v_key_375_);
v___x_381_ = lean_unsigned_to_nat(0u);
v_entry_382_ = lean_array_fget(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_array_fget_borrowed(v_entries_378_, v_entry_382_);
lean_dec(v_entry_382_);
v_snd_384_ = lean_ctor_get(v___x_383_, 1);
lean_inc(v_snd_384_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_snd_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_map_390_, lean_object* v_key_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_386_, v_00_u03b2_387_, v_inst_388_, v_inst_389_, v_map_390_, v_key_391_);
lean_dec_ref(v_map_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_393_, lean_object* v_value_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_a_397_, lean_object* v_x_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
lean_inc(v_a_397_);
v___x_400_ = lean_apply_2(v_inst_393_, v_a_397_, v_value_394_);
v___x_401_ = lean_unbox(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_a_397_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_395_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec_ref(v___x_395_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v_a_397_);
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_396_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_407_, lean_object* v_value_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_a_411_, lean_object* v_x_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_407_, v_value_408_, v___x_409_, v___x_410_, v_a_411_, v_x_412_, v___y_413_);
lean_dec_ref(v___y_413_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_map_420_, lean_object* v_inst_421_, lean_object* v_key_422_, lean_object* v_value_423_){
_start:
{
uint8_t v___x_424_; 
lean_inc(v_key_422_);
lean_inc_ref(v_inst_419_);
lean_inc_ref(v_inst_418_);
v___x_424_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_418_, v_inst_419_, v_key_422_, v_map_420_);
if (v___x_424_ == 0)
{
lean_dec(v_value_423_);
lean_dec(v_key_422_);
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_map_420_);
lean_dec_ref(v_inst_419_);
lean_dec_ref(v_inst_418_);
return v___x_424_;
}
else
{
lean_object* v_entries_425_; lean_object* v_indexes_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; size_t v_sz_430_; size_t v___x_431_; lean_object* v_entries_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___f_435_; size_t v_sz_436_; lean_object* v___x_437_; lean_object* v_fst_438_; 
v_entries_425_ = lean_ctor_get(v_map_420_, 0);
lean_inc_ref(v_entries_425_);
v_indexes_426_ = lean_ctor_get(v_map_420_, 1);
lean_inc_ref(v_indexes_426_);
lean_dec_ref(v_map_420_);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_418_, v_inst_419_, v_indexes_426_, v_key_422_);
lean_dec_ref(v_indexes_426_);
lean_inc_n(v___x_427_, 2);
v___f_428_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_428_, 0, v___x_427_);
lean_closure_set(v___f_428_, 1, v_entries_425_);
v___x_429_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_430_ = lean_array_size(v___x_427_);
v___x_431_ = ((size_t)0ULL);
v_entries_432_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v___x_427_, v___f_428_, v_sz_430_, v___x_431_, v___x_427_);
lean_dec(v___x_427_);
v___x_433_ = lean_box(0);
v___x_434_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_435_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_435_, 0, v_inst_421_);
lean_closure_set(v___f_435_, 1, v_value_423_);
lean_closure_set(v___f_435_, 2, v___x_434_);
lean_closure_set(v___f_435_, 3, v___x_433_);
v_sz_436_ = lean_array_size(v_entries_432_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_429_, v_entries_432_, v___f_435_, v_sz_436_, v___x_431_, v___x_434_);
v_fst_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_fst_438_);
lean_dec(v___x_437_);
if (lean_obj_tag(v_fst_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
else
{
lean_object* v_val_440_; 
v_val_440_ = lean_ctor_get(v_fst_438_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_fst_438_, 1);
if (lean_obj_tag(v_val_440_) == 0)
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
else
{
lean_dec_ref_known(v_val_440_, 1);
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_map_444_, lean_object* v_inst_445_, lean_object* v_key_446_, lean_object* v_value_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_442_, v_inst_443_, v_map_444_, v_inst_445_, v_key_446_, v_value_447_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_450_, lean_object* v_00_u03b2_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_map_454_, lean_object* v_inst_455_, lean_object* v_key_456_, lean_object* v_value_457_){
_start:
{
uint8_t v___x_458_; 
lean_inc(v_key_456_);
lean_inc_ref(v_inst_453_);
lean_inc_ref(v_inst_452_);
v___x_458_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_452_, v_inst_453_, v_key_456_, v_map_454_);
if (v___x_458_ == 0)
{
lean_dec(v_value_457_);
lean_dec(v_key_456_);
lean_dec_ref(v_inst_455_);
lean_dec_ref(v_map_454_);
lean_dec_ref(v_inst_453_);
lean_dec_ref(v_inst_452_);
return v___x_458_;
}
else
{
lean_object* v_entries_459_; lean_object* v_indexes_460_; lean_object* v___x_461_; lean_object* v___f_462_; lean_object* v___x_463_; size_t v_sz_464_; size_t v___x_465_; lean_object* v_entries_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___f_469_; size_t v_sz_470_; lean_object* v___x_471_; lean_object* v_fst_472_; 
v_entries_459_ = lean_ctor_get(v_map_454_, 0);
lean_inc_ref(v_entries_459_);
v_indexes_460_ = lean_ctor_get(v_map_454_, 1);
lean_inc_ref(v_indexes_460_);
lean_dec_ref(v_map_454_);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_452_, v_inst_453_, v_indexes_460_, v_key_456_);
lean_dec_ref(v_indexes_460_);
lean_inc_n(v___x_461_, 2);
v___f_462_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_462_, 0, v___x_461_);
lean_closure_set(v___f_462_, 1, v_entries_459_);
v___x_463_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_464_ = lean_array_size(v___x_461_);
v___x_465_ = ((size_t)0ULL);
v_entries_466_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_463_, v___x_461_, v___f_462_, v_sz_464_, v___x_465_, v___x_461_);
lean_dec(v___x_461_);
v___x_467_ = lean_box(0);
v___x_468_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_469_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_469_, 0, v_inst_455_);
lean_closure_set(v___f_469_, 1, v_value_457_);
lean_closure_set(v___f_469_, 2, v___x_468_);
lean_closure_set(v___f_469_, 3, v___x_467_);
v_sz_470_ = lean_array_size(v_entries_466_);
v___x_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_463_, v_entries_466_, v___f_469_, v_sz_470_, v___x_465_, v___x_468_);
v_fst_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_fst_472_);
lean_dec(v___x_471_);
if (lean_obj_tag(v_fst_472_) == 0)
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v_fst_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_fst_472_, 1);
if (lean_obj_tag(v_val_474_) == 0)
{
uint8_t v___x_475_; 
v___x_475_ = 0;
return v___x_475_;
}
else
{
lean_dec_ref_known(v_val_474_, 1);
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_476_, lean_object* v_00_u03b2_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_map_480_, lean_object* v_inst_481_, lean_object* v_key_482_, lean_object* v_value_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_476_, v_00_u03b2_477_, v_inst_478_, v_inst_479_, v_map_480_, v_inst_481_, v_key_482_, v_value_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_map_488_, lean_object* v_key_489_){
_start:
{
uint8_t v___x_490_; 
lean_inc(v_key_489_);
lean_inc_ref(v_inst_487_);
lean_inc_ref(v_inst_486_);
v___x_490_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_486_, v_inst_487_, v_key_489_, v_map_488_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v_key_489_);
lean_dec_ref(v_map_488_);
lean_dec_ref(v_inst_487_);
lean_dec_ref(v_inst_486_);
v___x_491_ = lean_box(0);
return v___x_491_;
}
else
{
lean_object* v_entries_492_; lean_object* v_indexes_493_; lean_object* v___x_494_; lean_object* v___f_495_; lean_object* v___x_496_; size_t v_sz_497_; size_t v___x_498_; lean_object* v_entries_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_entries_492_ = lean_ctor_get(v_map_488_, 0);
lean_inc_ref(v_entries_492_);
v_indexes_493_ = lean_ctor_get(v_map_488_, 1);
lean_inc_ref(v_indexes_493_);
lean_dec_ref(v_map_488_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_486_, v_inst_487_, v_indexes_493_, v_key_489_);
lean_dec_ref(v_indexes_493_);
lean_inc_n(v___x_494_, 2);
v___f_495_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_495_, 0, v___x_494_);
lean_closure_set(v___f_495_, 1, v_entries_492_);
v___x_496_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_497_ = lean_array_size(v___x_494_);
v___x_498_ = ((size_t)0ULL);
v_entries_499_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_496_, v___x_494_, v___f_495_, v_sz_497_, v___x_498_, v___x_494_);
lean_dec(v___x_494_);
v___x_500_ = lean_array_get_size(v_entries_499_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_nat_dec_lt(v___x_502_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec(v___x_502_);
lean_dec(v_entries_499_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_fget(v_entries_499_, v___x_502_);
lean_dec(v___x_502_);
lean_dec(v_entries_499_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_507_, lean_object* v_00_u03b2_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_map_511_, lean_object* v_key_512_){
_start:
{
uint8_t v___x_513_; 
lean_inc(v_key_512_);
lean_inc_ref(v_inst_510_);
lean_inc_ref(v_inst_509_);
v___x_513_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_509_, v_inst_510_, v_key_512_, v_map_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_key_512_);
lean_dec_ref(v_map_511_);
lean_dec_ref(v_inst_510_);
lean_dec_ref(v_inst_509_);
v___x_514_ = lean_box(0);
return v___x_514_;
}
else
{
lean_object* v_entries_515_; lean_object* v_indexes_516_; lean_object* v___x_517_; lean_object* v___f_518_; lean_object* v___x_519_; size_t v_sz_520_; size_t v___x_521_; lean_object* v_entries_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_entries_515_ = lean_ctor_get(v_map_511_, 0);
lean_inc_ref(v_entries_515_);
v_indexes_516_ = lean_ctor_get(v_map_511_, 1);
lean_inc_ref(v_indexes_516_);
lean_dec_ref(v_map_511_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_509_, v_inst_510_, v_indexes_516_, v_key_512_);
lean_dec_ref(v_indexes_516_);
lean_inc_n(v___x_517_, 2);
v___f_518_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_518_, 0, v___x_517_);
lean_closure_set(v___f_518_, 1, v_entries_515_);
v___x_519_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_520_ = lean_array_size(v___x_517_);
v___x_521_ = ((size_t)0ULL);
v_entries_522_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_519_, v___x_517_, v___f_518_, v_sz_520_, v___x_521_, v___x_517_);
lean_dec(v___x_517_);
v___x_523_ = lean_array_get_size(v_entries_522_);
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_sub(v___x_523_, v___x_524_);
v___x_526_ = lean_nat_dec_lt(v___x_525_, v___x_523_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v___x_525_);
lean_dec(v_entries_522_);
v___x_527_ = lean_box(0);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_array_fget(v_entries_522_, v___x_525_);
lean_dec(v___x_525_);
lean_dec(v_entries_522_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_map_532_, lean_object* v_key_533_, lean_object* v_d_534_){
_start:
{
uint8_t v___x_535_; 
lean_inc(v_key_533_);
lean_inc_ref(v_inst_531_);
lean_inc_ref(v_inst_530_);
v___x_535_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_530_, v_inst_531_, v_key_533_, v_map_532_);
if (v___x_535_ == 0)
{
lean_dec(v_key_533_);
lean_dec_ref(v_inst_531_);
lean_dec_ref(v_inst_530_);
lean_inc(v_d_534_);
return v_d_534_;
}
else
{
lean_object* v_entries_536_; lean_object* v_indexes_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v_entry_540_; lean_object* v___x_541_; lean_object* v_snd_542_; 
v_entries_536_ = lean_ctor_get(v_map_532_, 0);
v_indexes_537_ = lean_ctor_get(v_map_532_, 1);
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_530_, v_inst_531_, v_indexes_537_, v_key_533_);
v___x_539_ = lean_unsigned_to_nat(0u);
v_entry_540_ = lean_array_fget(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_array_fget_borrowed(v_entries_536_, v_entry_540_);
lean_dec(v_entry_540_);
v_snd_542_ = lean_ctor_get(v___x_541_, 1);
lean_inc(v_snd_542_);
return v_snd_542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_map_545_, lean_object* v_key_546_, lean_object* v_d_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_543_, v_inst_544_, v_map_545_, v_key_546_, v_d_547_);
lean_dec(v_d_547_);
lean_dec_ref(v_map_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_map_553_, lean_object* v_key_554_, lean_object* v_d_555_){
_start:
{
uint8_t v___x_556_; 
lean_inc(v_key_554_);
lean_inc_ref(v_inst_552_);
lean_inc_ref(v_inst_551_);
v___x_556_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_551_, v_inst_552_, v_key_554_, v_map_553_);
if (v___x_556_ == 0)
{
lean_dec(v_key_554_);
lean_dec_ref(v_inst_552_);
lean_dec_ref(v_inst_551_);
lean_inc(v_d_555_);
return v_d_555_;
}
else
{
lean_object* v_entries_557_; lean_object* v_indexes_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_entry_561_; lean_object* v___x_562_; lean_object* v_snd_563_; 
v_entries_557_ = lean_ctor_get(v_map_553_, 0);
v_indexes_558_ = lean_ctor_get(v_map_553_, 1);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_551_, v_inst_552_, v_indexes_558_, v_key_554_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_entry_561_ = lean_array_fget(v___x_559_, v___x_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_array_fget_borrowed(v_entries_557_, v_entry_561_);
lean_dec(v_entry_561_);
v_snd_563_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_snd_563_);
return v_snd_563_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_map_568_, lean_object* v_key_569_, lean_object* v_d_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_564_, v_00_u03b2_565_, v_inst_566_, v_inst_567_, v_map_568_, v_key_569_, v_d_570_);
lean_dec(v_d_570_);
lean_dec_ref(v_map_568_);
return v_res_571_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_575_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_576_ = lean_unsigned_to_nat(14u);
v___x_577_ = lean_unsigned_to_nat(22u);
v___x_578_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_579_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_580_ = l_mkPanicMessageWithDecl(v___x_579_, v___x_578_, v___x_577_, v___x_576_, v___x_575_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_map_584_, lean_object* v_key_585_){
_start:
{
uint8_t v___x_586_; 
lean_inc(v_key_585_);
lean_inc_ref(v_inst_582_);
lean_inc_ref(v_inst_581_);
v___x_586_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_581_, v_inst_582_, v_key_585_, v_map_584_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_key_585_);
lean_dec_ref(v_inst_582_);
lean_dec_ref(v_inst_581_);
v___x_587_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_588_ = l_panic___redArg(v_inst_583_, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v_entries_589_; lean_object* v_indexes_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_entry_593_; lean_object* v___x_594_; lean_object* v_snd_595_; 
v_entries_589_ = lean_ctor_get(v_map_584_, 0);
v_indexes_590_ = lean_ctor_get(v_map_584_, 1);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_581_, v_inst_582_, v_indexes_590_, v_key_585_);
v___x_592_ = lean_unsigned_to_nat(0u);
v_entry_593_ = lean_array_fget(v___x_591_, v___x_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_array_fget_borrowed(v_entries_589_, v_entry_593_);
lean_dec(v_entry_593_);
v_snd_595_ = lean_ctor_get(v___x_594_, 1);
lean_inc(v_snd_595_);
return v_snd_595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_map_599_, lean_object* v_key_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_596_, v_inst_597_, v_inst_598_, v_map_599_, v_key_600_);
lean_dec_ref(v_map_599_);
lean_dec(v_inst_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_map_607_, lean_object* v_key_608_){
_start:
{
uint8_t v___x_609_; 
lean_inc(v_key_608_);
lean_inc_ref(v_inst_605_);
lean_inc_ref(v_inst_604_);
v___x_609_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_604_, v_inst_605_, v_key_608_, v_map_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
lean_dec(v_key_608_);
lean_dec_ref(v_inst_605_);
lean_dec_ref(v_inst_604_);
v___x_610_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_611_ = l_panic___redArg(v_inst_606_, v___x_610_);
return v___x_611_;
}
else
{
lean_object* v_entries_612_; lean_object* v_indexes_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_entry_616_; lean_object* v___x_617_; lean_object* v_snd_618_; 
v_entries_612_ = lean_ctor_get(v_map_607_, 0);
v_indexes_613_ = lean_ctor_get(v_map_607_, 1);
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_604_, v_inst_605_, v_indexes_613_, v_key_608_);
v___x_615_ = lean_unsigned_to_nat(0u);
v_entry_616_ = lean_array_fget(v___x_614_, v___x_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_array_fget_borrowed(v_entries_612_, v_entry_616_);
lean_dec(v_entry_616_);
v_snd_618_ = lean_ctor_get(v___x_617_, 1);
lean_inc(v_snd_618_);
return v_snd_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_map_624_, lean_object* v_key_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_619_, v_00_u03b2_620_, v_inst_621_, v_inst_622_, v_inst_623_, v_map_624_, v_key_625_);
lean_dec_ref(v_map_624_);
lean_dec(v_inst_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
lean_dec(v_h__1_628_);
v___x_630_ = lean_box(0);
v___x_631_ = lean_apply_1(v_h__2_629_, v___x_630_);
return v___x_631_;
}
else
{
lean_object* v_val_632_; lean_object* v___x_633_; 
lean_dec(v_h__2_629_);
v_val_632_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v_x_627_, 1);
v___x_633_ = lean_apply_1(v_h__1_628_, v_val_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_634_, lean_object* v_x_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v_h__1_636_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_apply_1(v_h__2_637_, v___x_638_);
return v___x_639_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; 
lean_dec(v_h__2_637_);
v_val_640_ = lean_ctor_get(v_x_635_, 0);
lean_inc(v_val_640_);
lean_dec_ref_known(v_x_635_, 1);
v___x_641_ = lean_apply_1(v_h__1_636_, v_val_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_mk_empty_array_with_capacity(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v_i_642_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
else
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
v_val_648_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v_x_643_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v_x_643_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_652_ = lean_array_push(v_val_648_, v_i_642_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_map_659_, lean_object* v_key_660_, lean_object* v_value_661_){
_start:
{
lean_object* v_entries_662_; lean_object* v_indexes_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v_entries_662_ = lean_ctor_get(v_map_659_, 0);
v_indexes_663_ = lean_ctor_get(v_map_659_, 1);
v_isSharedCheck_675_ = !lean_is_exclusive(v_map_659_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v_map_659_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_indexes_663_);
lean_inc(v_entries_662_);
lean_dec(v_map_659_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_i_667_; lean_object* v_f_668_; lean_object* v___x_669_; lean_object* v_entries_670_; lean_object* v_indexes_671_; lean_object* v___x_673_; 
v_i_667_ = lean_array_get_size(v_entries_662_);
v_f_668_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_668_, 0, v_i_667_);
lean_inc(v_key_660_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_key_660_);
lean_ctor_set(v___x_669_, 1, v_value_661_);
v_entries_670_ = lean_array_push(v_entries_662_, v___x_669_);
v_indexes_671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_657_, v_inst_658_, v_indexes_663_, v_key_660_, v_f_668_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v_indexes_671_);
lean_ctor_set(v___x_665_, 0, v_entries_670_);
v___x_673_ = v___x_665_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_entries_670_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_indexes_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_map_682_, lean_object* v_key_683_, lean_object* v_value_684_){
_start:
{
lean_object* v_entries_685_; lean_object* v_indexes_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_698_; 
v_entries_685_ = lean_ctor_get(v_map_682_, 0);
v_indexes_686_ = lean_ctor_get(v_map_682_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_map_682_);
if (v_isSharedCheck_698_ == 0)
{
v___x_688_ = v_map_682_;
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_indexes_686_);
lean_inc(v_entries_685_);
lean_dec(v_map_682_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_698_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_i_690_; lean_object* v_f_691_; lean_object* v___x_692_; lean_object* v_entries_693_; lean_object* v_indexes_694_; lean_object* v___x_696_; 
v_i_690_ = lean_array_get_size(v_entries_685_);
v_f_691_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_691_, 0, v_i_690_);
lean_inc(v_key_683_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v_key_683_);
lean_ctor_set(v___x_692_, 1, v_value_684_);
v_entries_693_ = lean_array_push(v_entries_685_, v___x_692_);
v_indexes_694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_678_, v_inst_679_, v_indexes_686_, v_key_683_, v_f_691_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_indexes_694_);
lean_ctor_set(v___x_688_, 0, v_entries_693_);
v___x_696_ = v___x_688_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_entries_693_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_indexes_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_x1_702_, lean_object* v_x2_703_){
_start:
{
lean_object* v_entries_704_; lean_object* v_indexes_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_717_; 
v_entries_704_ = lean_ctor_get(v_x1_702_, 0);
v_indexes_705_ = lean_ctor_get(v_x1_702_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_x1_702_);
if (v_isSharedCheck_717_ == 0)
{
v___x_707_ = v_x1_702_;
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_indexes_705_);
lean_inc(v_entries_704_);
lean_dec(v_x1_702_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_717_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_i_709_; lean_object* v_f_710_; lean_object* v___x_711_; lean_object* v_entries_712_; lean_object* v_indexes_713_; lean_object* v___x_715_; 
v_i_709_ = lean_array_get_size(v_entries_704_);
v_f_710_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_710_, 0, v_i_709_);
lean_inc(v_key_699_);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_key_699_);
lean_ctor_set(v___x_711_, 1, v_x2_703_);
v_entries_712_ = lean_array_push(v_entries_704_, v___x_711_);
v_indexes_713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_700_, v_inst_701_, v_indexes_705_, v_key_699_, v_f_710_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v_indexes_713_);
lean_ctor_set(v___x_707_, 0, v_entries_712_);
v___x_715_ = v___x_707_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_entries_712_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_indexes_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_map_720_, lean_object* v_key_721_, lean_object* v_values_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_array_get_size(v_values_722_);
v___x_725_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_726_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_726_ == 0)
{
lean_dec_ref(v_values_722_);
lean_dec(v_key_721_);
lean_dec_ref(v_inst_719_);
lean_dec_ref(v_inst_718_);
return v_map_720_;
}
else
{
lean_object* v___f_727_; uint8_t v___x_728_; 
v___f_727_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_727_, 0, v_key_721_);
lean_closure_set(v___f_727_, 1, v_inst_718_);
lean_closure_set(v___f_727_, 2, v_inst_719_);
v___x_728_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_728_ == 0)
{
if (v___x_726_ == 0)
{
lean_dec_ref(v___f_727_);
lean_dec_ref(v_values_722_);
return v_map_720_;
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_724_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_725_, v___f_727_, v_values_722_, v___x_729_, v___x_730_, v_map_720_);
return v___x_731_;
}
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_724_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_725_, v___f_727_, v_values_722_, v___x_732_, v___x_733_, v_map_720_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_map_741_, lean_object* v_key_742_, lean_object* v_values_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_values_743_);
v___x_746_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_747_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_values_743_);
lean_dec(v_key_742_);
lean_dec_ref(v_inst_738_);
lean_dec_ref(v_inst_737_);
return v_map_741_;
}
else
{
lean_object* v___f_748_; uint8_t v___x_749_; 
v___f_748_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_748_, 0, v_key_742_);
lean_closure_set(v___f_748_, 1, v_inst_737_);
lean_closure_set(v___f_748_, 2, v_inst_738_);
v___x_749_ = lean_nat_dec_le(v___x_745_, v___x_745_);
if (v___x_749_ == 0)
{
if (v___x_747_ == 0)
{
lean_dec_ref(v___f_748_);
lean_dec_ref(v_values_743_);
return v_map_741_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_745_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_746_, v___f_748_, v_values_743_, v___x_750_, v___x_751_, v_map_741_);
return v___x_752_;
}
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_745_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_746_, v___f_748_, v_values_743_, v___x_753_, v___x_754_, v_map_741_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_inst_758_, lean_object* v_inst_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_761_, lean_object* v_00_u03b2_762_, lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_761_, v_00_u03b2_762_, v_inst_763_, v_inst_764_);
lean_dec_ref(v_inst_764_);
lean_dec_ref(v_inst_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_acc_768_, lean_object* v_x_769_){
_start:
{
lean_object* v_fst_770_; lean_object* v_entries_771_; lean_object* v_indexes_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v_fst_770_ = lean_ctor_get(v_x_769_, 0);
lean_inc(v_fst_770_);
v_entries_771_ = lean_ctor_get(v_acc_768_, 0);
v_indexes_772_ = lean_ctor_get(v_acc_768_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_acc_768_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_acc_768_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_indexes_772_);
lean_inc(v_entries_771_);
lean_dec(v_acc_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_i_776_; lean_object* v_f_777_; lean_object* v_entries_778_; lean_object* v_indexes_779_; lean_object* v___x_781_; 
v_i_776_ = lean_array_get_size(v_entries_771_);
v_f_777_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_777_, 0, v_i_776_);
v_entries_778_ = lean_array_push(v_entries_771_, v_x_769_);
v_indexes_779_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_766_, v_inst_767_, v_indexes_772_, v_fst_770_, v_f_777_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_indexes_779_);
lean_ctor_set(v___x_774_, 0, v_entries_778_);
v___x_781_ = v___x_774_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_entries_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_indexes_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_pairs_786_){
_start:
{
lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_inc_ref(v_inst_785_);
lean_inc_ref(v_inst_784_);
v___f_787_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_787_, 0, v_inst_784_);
lean_closure_set(v___f_787_, 1, v_inst_785_);
v___x_788_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_784_, v_inst_785_);
lean_dec_ref(v_inst_785_);
lean_dec_ref(v_inst_784_);
v___x_789_ = l_List_foldl___redArg(v___f_787_, v___x_788_, v_pairs_786_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_pairs_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_792_, v_inst_793_, v_pairs_796_);
return v___x_797_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_map_800_, lean_object* v_key_801_){
_start:
{
lean_object* v_indexes_802_; uint8_t v___x_803_; 
v_indexes_802_ = lean_ctor_get(v_map_800_, 1);
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_798_, v_inst_799_, v_indexes_802_, v_key_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_map_806_, lean_object* v_key_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_804_, v_inst_805_, v_map_806_, v_key_807_);
lean_dec_ref(v_map_806_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_map_814_, lean_object* v_key_815_){
_start:
{
lean_object* v_indexes_816_; uint8_t v___x_817_; 
v_indexes_816_ = lean_ctor_get(v_map_814_, 1);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_812_, v_inst_813_, v_indexes_816_, v_key_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_map_822_, lean_object* v_key_823_){
_start:
{
uint8_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_818_, v_00_u03b2_819_, v_inst_820_, v_inst_821_, v_map_822_, v_key_823_);
lean_dec_ref(v_map_822_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_key_828_, lean_object* v_f_829_, lean_object* v_x1_830_, lean_object* v_x2_831_){
_start:
{
lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_858_; 
v_fst_832_ = lean_ctor_get(v_x2_831_, 0);
v_snd_833_ = lean_ctor_get(v_x2_831_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_x2_831_);
if (v_isSharedCheck_858_ == 0)
{
v___x_835_ = v_x2_831_;
v_isShared_836_ = v_isSharedCheck_858_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_snd_833_);
lean_inc(v_fst_832_);
lean_dec(v_x2_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_858_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___y_838_; lean_object* v___x_855_; uint8_t v___x_856_; 
lean_inc_ref(v_inst_826_);
lean_inc(v_fst_832_);
v___x_855_ = lean_apply_2(v_inst_826_, v_fst_832_, v_key_828_);
v___x_856_ = lean_unbox(v___x_855_);
if (v___x_856_ == 0)
{
lean_dec(v_f_829_);
v___y_838_ = v_snd_833_;
goto v___jp_837_;
}
else
{
lean_object* v___x_857_; 
v___x_857_ = lean_apply_1(v_f_829_, v_snd_833_);
v___y_838_ = v___x_857_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v_entries_839_; lean_object* v_indexes_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_854_; 
v_entries_839_ = lean_ctor_get(v_x1_830_, 0);
v_indexes_840_ = lean_ctor_get(v_x1_830_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x1_830_);
if (v_isSharedCheck_854_ == 0)
{
v___x_842_ = v_x1_830_;
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_indexes_840_);
lean_inc(v_entries_839_);
lean_dec(v_x1_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_854_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_i_844_; lean_object* v_f_845_; lean_object* v___x_847_; 
v_i_844_ = lean_array_get_size(v_entries_839_);
v_f_845_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_845_, 0, v_i_844_);
lean_inc(v_fst_832_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___y_838_);
v___x_847_ = v___x_835_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_fst_832_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___y_838_);
v___x_847_ = v_reuseFailAlloc_853_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v_entries_848_; lean_object* v_indexes_849_; lean_object* v___x_851_; 
v_entries_848_ = lean_array_push(v_entries_839_, v___x_847_);
v_indexes_849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_826_, v_inst_827_, v_indexes_840_, v_fst_832_, v_f_845_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_indexes_849_);
lean_ctor_set(v___x_842_, 0, v_entries_848_);
v___x_851_ = v___x_842_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_entries_848_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_indexes_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_map_861_, lean_object* v_key_862_, lean_object* v_f_863_){
_start:
{
uint8_t v___x_864_; 
lean_inc(v_key_862_);
lean_inc_ref(v_inst_860_);
lean_inc_ref(v_inst_859_);
v___x_864_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_859_, v_inst_860_, v_key_862_, v_map_861_);
if (v___x_864_ == 0)
{
lean_dec(v_f_863_);
lean_dec(v_key_862_);
lean_dec_ref(v_inst_860_);
lean_dec_ref(v_inst_859_);
return v_map_861_;
}
else
{
lean_object* v_entries_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_entries_865_ = lean_ctor_get(v_map_861_, 0);
lean_inc_ref(v_entries_865_);
lean_dec_ref(v_map_861_);
v___x_866_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_859_, v_inst_860_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_entries_865_);
v___x_869_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_870_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_870_ == 0)
{
lean_dec_ref(v_entries_865_);
lean_dec(v_f_863_);
lean_dec(v_key_862_);
lean_dec_ref(v_inst_860_);
lean_dec_ref(v_inst_859_);
return v___x_866_;
}
else
{
lean_object* v___f_871_; uint8_t v___x_872_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_871_, 0, v_inst_859_);
lean_closure_set(v___f_871_, 1, v_inst_860_);
lean_closure_set(v___f_871_, 2, v_key_862_);
lean_closure_set(v___f_871_, 3, v_f_863_);
v___x_872_ = lean_nat_dec_le(v___x_868_, v___x_868_);
if (v___x_872_ == 0)
{
if (v___x_870_ == 0)
{
lean_dec_ref(v___f_871_);
lean_dec_ref(v_entries_865_);
return v___x_866_;
}
else
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)0ULL);
v___x_874_ = lean_usize_of_nat(v___x_868_);
v___x_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_869_, v___f_871_, v_entries_865_, v___x_873_, v___x_874_, v___x_866_);
return v___x_875_;
}
}
else
{
size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; 
v___x_876_ = ((size_t)0ULL);
v___x_877_ = lean_usize_of_nat(v___x_868_);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_869_, v___f_871_, v_entries_865_, v___x_876_, v___x_877_, v___x_866_);
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_inst_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_map_885_, lean_object* v_key_886_, lean_object* v_f_887_){
_start:
{
uint8_t v___x_888_; 
lean_inc(v_key_886_);
lean_inc_ref(v_inst_882_);
lean_inc_ref(v_inst_881_);
v___x_888_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_881_, v_inst_882_, v_key_886_, v_map_885_);
if (v___x_888_ == 0)
{
lean_dec(v_f_887_);
lean_dec(v_key_886_);
lean_dec_ref(v_inst_882_);
lean_dec_ref(v_inst_881_);
return v_map_885_;
}
else
{
lean_object* v_entries_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_entries_889_ = lean_ctor_get(v_map_885_, 0);
lean_inc_ref(v_entries_889_);
lean_dec_ref(v_map_885_);
v___x_890_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_881_, v_inst_882_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = lean_array_get_size(v_entries_889_);
v___x_893_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_894_ = lean_nat_dec_lt(v___x_891_, v___x_892_);
if (v___x_894_ == 0)
{
lean_dec_ref(v_entries_889_);
lean_dec(v_f_887_);
lean_dec(v_key_886_);
lean_dec_ref(v_inst_882_);
lean_dec_ref(v_inst_881_);
return v___x_890_;
}
else
{
lean_object* v___f_895_; uint8_t v___x_896_; 
v___f_895_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_895_, 0, v_inst_881_);
lean_closure_set(v___f_895_, 1, v_inst_882_);
lean_closure_set(v___f_895_, 2, v_key_886_);
lean_closure_set(v___f_895_, 3, v_f_887_);
v___x_896_ = lean_nat_dec_le(v___x_892_, v___x_892_);
if (v___x_896_ == 0)
{
if (v___x_894_ == 0)
{
lean_dec_ref(v___f_895_);
lean_dec_ref(v_entries_889_);
return v___x_890_;
}
else
{
size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((size_t)0ULL);
v___x_898_ = lean_usize_of_nat(v___x_892_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_893_, v___f_895_, v_entries_889_, v___x_897_, v___x_898_, v___x_890_);
return v___x_899_;
}
}
else
{
size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; 
v___x_900_ = ((size_t)0ULL);
v___x_901_ = lean_usize_of_nat(v___x_892_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_893_, v___f_895_, v_entries_889_, v___x_900_, v___x_901_, v___x_890_);
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_map_905_, lean_object* v_key_906_, lean_object* v_value_907_){
_start:
{
uint8_t v___x_908_; 
lean_inc(v_key_906_);
lean_inc_ref(v_inst_904_);
lean_inc_ref(v_inst_903_);
v___x_908_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_903_, v_inst_904_, v_key_906_, v_map_905_);
if (v___x_908_ == 0)
{
lean_dec(v_value_907_);
lean_dec(v_key_906_);
lean_dec_ref(v_inst_904_);
lean_dec_ref(v_inst_903_);
return v_map_905_;
}
else
{
lean_object* v_entries_909_; lean_object* v_indexes_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_924_; 
v_entries_909_ = lean_ctor_get(v_map_905_, 0);
v_indexes_910_ = lean_ctor_get(v_map_905_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_map_905_);
if (v_isSharedCheck_924_ == 0)
{
v___x_912_ = v_map_905_;
v_isShared_913_ = v_isSharedCheck_924_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_indexes_910_);
lean_inc(v_entries_909_);
lean_dec(v_map_905_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_924_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_idxs_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_lastIdx_918_; lean_object* v___x_919_; lean_object* v_entries_920_; lean_object* v___x_922_; 
lean_inc(v_key_906_);
v_idxs_914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_903_, v_inst_904_, v_indexes_910_, v_key_906_);
v___x_915_ = lean_array_get_size(v_idxs_914_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_sub(v___x_915_, v___x_916_);
v_lastIdx_918_ = lean_array_fget(v_idxs_914_, v___x_917_);
lean_dec(v___x_917_);
lean_dec(v_idxs_914_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_key_906_);
lean_ctor_set(v___x_919_, 1, v_value_907_);
v_entries_920_ = lean_array_fset(v_entries_909_, v_lastIdx_918_, v___x_919_);
lean_dec(v_lastIdx_918_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v_entries_920_);
v___x_922_ = v___x_912_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_entries_920_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_indexes_910_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_inst_927_, lean_object* v_inst_928_, lean_object* v_map_929_, lean_object* v_key_930_, lean_object* v_value_931_){
_start:
{
uint8_t v___x_932_; 
lean_inc(v_key_930_);
lean_inc_ref(v_inst_928_);
lean_inc_ref(v_inst_927_);
v___x_932_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_927_, v_inst_928_, v_key_930_, v_map_929_);
if (v___x_932_ == 0)
{
lean_dec(v_value_931_);
lean_dec(v_key_930_);
lean_dec_ref(v_inst_928_);
lean_dec_ref(v_inst_927_);
return v_map_929_;
}
else
{
lean_object* v_entries_933_; lean_object* v_indexes_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_948_; 
v_entries_933_ = lean_ctor_get(v_map_929_, 0);
v_indexes_934_ = lean_ctor_get(v_map_929_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_map_929_);
if (v_isSharedCheck_948_ == 0)
{
v___x_936_ = v_map_929_;
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_indexes_934_);
lean_inc(v_entries_933_);
lean_dec(v_map_929_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_948_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_idxs_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_lastIdx_942_; lean_object* v___x_943_; lean_object* v_entries_944_; lean_object* v___x_946_; 
lean_inc(v_key_930_);
v_idxs_938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_927_, v_inst_928_, v_indexes_934_, v_key_930_);
v___x_939_ = lean_array_get_size(v_idxs_938_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_sub(v___x_939_, v___x_940_);
v_lastIdx_942_ = lean_array_fget(v_idxs_938_, v___x_941_);
lean_dec(v___x_941_);
lean_dec(v_idxs_938_);
v___x_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_943_, 0, v_key_930_);
lean_ctor_set(v___x_943_, 1, v_value_931_);
v_entries_944_ = lean_array_fset(v_entries_933_, v_lastIdx_942_, v___x_943_);
lean_dec(v_lastIdx_942_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_entries_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_entries_944_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_indexes_934_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_x1_951_, lean_object* v_x2_952_){
_start:
{
lean_object* v_fst_953_; lean_object* v_entries_954_; lean_object* v_indexes_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_966_; 
v_fst_953_ = lean_ctor_get(v_x2_952_, 0);
lean_inc(v_fst_953_);
v_entries_954_ = lean_ctor_get(v_x1_951_, 0);
v_indexes_955_ = lean_ctor_get(v_x1_951_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_x1_951_);
if (v_isSharedCheck_966_ == 0)
{
v___x_957_ = v_x1_951_;
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_indexes_955_);
lean_inc(v_entries_954_);
lean_dec(v_x1_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_966_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_i_959_; lean_object* v_f_960_; lean_object* v_entries_961_; lean_object* v_indexes_962_; lean_object* v___x_964_; 
v_i_959_ = lean_array_get_size(v_entries_954_);
v_f_960_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_960_, 0, v_i_959_);
v_entries_961_ = lean_array_push(v_entries_954_, v_x2_952_);
v_indexes_962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_949_, v_inst_950_, v_indexes_955_, v_fst_953_, v_f_960_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_indexes_962_);
lean_ctor_set(v___x_957_, 0, v_entries_961_);
v___x_964_ = v___x_957_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_entries_961_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_indexes_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__0(lean_object* v_inst_967_, lean_object* v_key_968_, lean_object* v_x1_969_, lean_object* v_x2_970_){
_start:
{
lean_object* v_fst_971_; lean_object* v___x_972_; uint8_t v___x_973_; 
v_fst_971_ = lean_ctor_get(v_x2_970_, 0);
lean_inc(v_fst_971_);
v___x_972_ = lean_apply_2(v_inst_967_, v_fst_971_, v_key_968_);
v___x_973_ = lean_unbox(v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_push(v_x1_969_, v_x2_970_);
return v___x_974_;
}
else
{
lean_dec_ref(v_x2_970_);
return v_x1_969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_map_977_, lean_object* v_key_978_){
_start:
{
uint8_t v___x_979_; 
lean_inc(v_key_978_);
lean_inc_ref(v_inst_976_);
lean_inc_ref(v_inst_975_);
v___x_979_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_975_, v_inst_976_, v_key_978_, v_map_977_);
if (v___x_979_ == 0)
{
lean_dec(v_key_978_);
lean_dec_ref(v_inst_976_);
lean_dec_ref(v_inst_975_);
return v_map_977_;
}
else
{
lean_object* v_entries_980_; lean_object* v___f_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___y_985_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_entries_980_ = lean_ctor_get(v_map_977_, 0);
lean_inc_ref(v_entries_980_);
lean_dec_ref(v_map_977_);
lean_inc_ref(v_inst_976_);
lean_inc_ref(v_inst_975_);
v___f_981_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_981_, 0, v_inst_975_);
lean_closure_set(v___f_981_, 1, v_inst_976_);
v___x_982_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_975_, v_inst_976_);
lean_dec_ref(v_inst_976_);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_array_get_size(v_entries_980_);
v___x_997_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_998_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_999_ = lean_nat_dec_lt(v___x_983_, v___x_996_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_entries_980_);
lean_dec(v_key_978_);
lean_dec_ref(v_inst_975_);
v___y_985_ = v___x_997_;
goto v___jp_984_;
}
else
{
lean_object* v___f_1000_; uint8_t v___x_1001_; 
v___f_1000_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1000_, 0, v_inst_975_);
lean_closure_set(v___f_1000_, 1, v_key_978_);
v___x_1001_ = lean_nat_dec_le(v___x_996_, v___x_996_);
if (v___x_1001_ == 0)
{
if (v___x_999_ == 0)
{
lean_dec_ref(v___f_1000_);
lean_dec_ref(v_entries_980_);
v___y_985_ = v___x_997_;
goto v___jp_984_;
}
else
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = lean_usize_of_nat(v___x_996_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_998_, v___f_1000_, v_entries_980_, v___x_1002_, v___x_1003_, v___x_997_);
v___y_985_ = v___x_1004_;
goto v___jp_984_;
}
}
else
{
size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = lean_usize_of_nat(v___x_996_);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_998_, v___f_1000_, v_entries_980_, v___x_1005_, v___x_1006_, v___x_997_);
v___y_985_ = v___x_1007_;
goto v___jp_984_;
}
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_986_ = lean_array_get_size(v___y_985_);
v___x_987_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_988_ = lean_nat_dec_lt(v___x_983_, v___x_986_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___y_985_);
lean_dec_ref(v___f_981_);
return v___x_982_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_le(v___x_986_, v___x_986_);
if (v___x_989_ == 0)
{
if (v___x_988_ == 0)
{
lean_dec_ref(v___y_985_);
lean_dec_ref(v___f_981_);
return v___x_982_;
}
else
{
size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_of_nat(v___x_986_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_987_, v___f_981_, v___y_985_, v___x_990_, v___x_991_, v___x_982_);
return v___x_992_;
}
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_986_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_987_, v___f_981_, v___y_985_, v___x_993_, v___x_994_, v___x_982_);
return v___x_995_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_map_1014_, lean_object* v_key_1015_){
_start:
{
uint8_t v___x_1016_; 
lean_inc(v_key_1015_);
lean_inc_ref(v_inst_1011_);
lean_inc_ref(v_inst_1010_);
v___x_1016_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1010_, v_inst_1011_, v_key_1015_, v_map_1014_);
if (v___x_1016_ == 0)
{
lean_dec(v_key_1015_);
lean_dec_ref(v_inst_1011_);
lean_dec_ref(v_inst_1010_);
return v_map_1014_;
}
else
{
lean_object* v_entries_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___y_1022_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_entries_1017_ = lean_ctor_get(v_map_1014_, 0);
lean_inc_ref(v_entries_1017_);
lean_dec_ref(v_map_1014_);
lean_inc_ref(v_inst_1011_);
lean_inc_ref(v_inst_1010_);
v___f_1018_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1018_, 0, v_inst_1010_);
lean_closure_set(v___f_1018_, 1, v_inst_1011_);
v___x_1019_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1010_, v_inst_1011_);
lean_dec_ref(v_inst_1011_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_array_get_size(v_entries_1017_);
v___x_1034_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_1035_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1036_ = lean_nat_dec_lt(v___x_1020_, v___x_1033_);
if (v___x_1036_ == 0)
{
lean_dec_ref(v_entries_1017_);
lean_dec(v_key_1015_);
lean_dec_ref(v_inst_1010_);
v___y_1022_ = v___x_1034_;
goto v___jp_1021_;
}
else
{
lean_object* v___f_1037_; uint8_t v___x_1038_; 
v___f_1037_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1037_, 0, v_inst_1010_);
lean_closure_set(v___f_1037_, 1, v_key_1015_);
v___x_1038_ = lean_nat_dec_le(v___x_1033_, v___x_1033_);
if (v___x_1038_ == 0)
{
if (v___x_1036_ == 0)
{
lean_dec_ref(v___f_1037_);
lean_dec_ref(v_entries_1017_);
v___y_1022_ = v___x_1034_;
goto v___jp_1021_;
}
else
{
size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = lean_usize_of_nat(v___x_1033_);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1035_, v___f_1037_, v_entries_1017_, v___x_1039_, v___x_1040_, v___x_1034_);
v___y_1022_ = v___x_1041_;
goto v___jp_1021_;
}
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = lean_usize_of_nat(v___x_1033_);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1035_, v___f_1037_, v_entries_1017_, v___x_1042_, v___x_1043_, v___x_1034_);
v___y_1022_ = v___x_1044_;
goto v___jp_1021_;
}
}
v___jp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1023_ = lean_array_get_size(v___y_1022_);
v___x_1024_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1025_ = lean_nat_dec_lt(v___x_1020_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_dec_ref(v___y_1022_);
lean_dec_ref(v___f_1018_);
return v___x_1019_;
}
else
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_nat_dec_le(v___x_1023_, v___x_1023_);
if (v___x_1026_ == 0)
{
if (v___x_1025_ == 0)
{
lean_dec_ref(v___y_1022_);
lean_dec_ref(v___f_1018_);
return v___x_1019_;
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1023_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1018_, v___y_1022_, v___x_1027_, v___x_1028_, v___x_1019_);
return v___x_1029_;
}
}
else
{
size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = lean_usize_of_nat(v___x_1023_);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1018_, v___y_1022_, v___x_1030_, v___x_1031_, v___x_1019_);
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1045_){
_start:
{
lean_object* v_entries_1046_; lean_object* v___x_1047_; 
v_entries_1046_ = lean_ctor_get(v_map_1045_, 0);
v___x_1047_ = lean_array_get_size(v_entries_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1048_);
lean_dec_ref(v_map_1048_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_map_1054_){
_start:
{
lean_object* v_entries_1055_; lean_object* v___x_1056_; 
v_entries_1055_ = lean_ctor_get(v_map_1054_, 0);
v___x_1056_ = lean_array_get_size(v_entries_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_inst_1060_, lean_object* v_map_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1057_, v_00_u03b2_1058_, v_inst_1059_, v_inst_1060_, v_map_1061_);
lean_dec_ref(v_map_1061_);
lean_dec_ref(v_inst_1060_);
lean_dec_ref(v_inst_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1063_){
_start:
{
lean_object* v_entries_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_entries_1064_ = lean_ctor_get(v_map_1063_, 0);
v___x_1065_ = lean_array_get_size(v_entries_1064_);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_nat_dec_eq(v___x_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1068_){
_start:
{
uint8_t v_res_1069_; lean_object* v_r_1070_; 
v_res_1069_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1068_);
lean_dec_ref(v_map_1068_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1071_, lean_object* v_00_u03b2_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_map_1075_){
_start:
{
lean_object* v_entries_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_entries_1076_ = lean_ctor_get(v_map_1075_, 0);
v___x_1077_ = lean_array_get_size(v_entries_1076_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_nat_dec_eq(v___x_1077_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_map_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1080_, v_00_u03b2_1081_, v_inst_1082_, v_inst_1083_, v_map_1084_);
lean_dec_ref(v_map_1084_);
lean_dec_ref(v_inst_1083_);
lean_dec_ref(v_inst_1082_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1087_){
_start:
{
lean_object* v_entries_1088_; 
v_entries_1088_ = lean_ctor_get(v_map_1087_, 0);
lean_inc_ref(v_entries_1088_);
return v_entries_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1089_);
lean_dec_ref(v_map_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_map_1095_){
_start:
{
lean_object* v_entries_1096_; 
v_entries_1096_ = lean_ctor_get(v_map_1095_, 0);
lean_inc_ref(v_entries_1096_);
return v_entries_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_map_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1097_, v_00_u03b2_1098_, v_inst_1099_, v_inst_1100_, v_map_1101_);
lean_dec_ref(v_map_1101_);
lean_dec_ref(v_inst_1100_);
lean_dec_ref(v_inst_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1103_){
_start:
{
lean_object* v_entries_1104_; lean_object* v___x_1105_; 
v_entries_1104_ = lean_ctor_get(v_map_1103_, 0);
lean_inc_ref(v_entries_1104_);
lean_dec_ref(v_map_1103_);
v___x_1105_ = lean_array_to_list(v_entries_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_map_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_map_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1112_, v_00_u03b2_1113_, v_inst_1114_, v_inst_1115_, v_map_1116_);
lean_dec_ref(v_inst_1115_);
lean_dec_ref(v_inst_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_m1_1120_, lean_object* v_m2_1121_){
_start:
{
lean_object* v_entries_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_entries_1122_ = lean_ctor_get(v_m2_1121_, 0);
lean_inc_ref(v_entries_1122_);
lean_dec_ref(v_m2_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_array_get_size(v_entries_1122_);
v___x_1125_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1126_ = lean_nat_dec_lt(v___x_1123_, v___x_1124_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_entries_1122_);
lean_dec_ref(v_inst_1119_);
lean_dec_ref(v_inst_1118_);
return v_m1_1120_;
}
else
{
lean_object* v___f_1127_; uint8_t v___x_1128_; 
v___f_1127_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1127_, 0, v_inst_1118_);
lean_closure_set(v___f_1127_, 1, v_inst_1119_);
v___x_1128_ = lean_nat_dec_le(v___x_1124_, v___x_1124_);
if (v___x_1128_ == 0)
{
if (v___x_1126_ == 0)
{
lean_dec_ref(v___f_1127_);
lean_dec_ref(v_entries_1122_);
return v_m1_1120_;
}
else
{
size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = ((size_t)0ULL);
v___x_1130_ = lean_usize_of_nat(v___x_1124_);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1125_, v___f_1127_, v_entries_1122_, v___x_1129_, v___x_1130_, v_m1_1120_);
return v___x_1131_;
}
}
else
{
size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = ((size_t)0ULL);
v___x_1133_ = lean_usize_of_nat(v___x_1124_);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1125_, v___f_1127_, v_entries_1122_, v___x_1132_, v___x_1133_, v_m1_1120_);
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_inst_1140_, lean_object* v_m1_1141_, lean_object* v_m2_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1137_, v_inst_1138_, v_m1_1141_, v_m2_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object* v_inst_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1144_, v_inst_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v_inst_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_1147_, v_inst_1148_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1152_, v_inst_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1155_, v_00_u03b2_1156_, v_inst_1157_, v_inst_1158_);
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_inst_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_fst_1163_; lean_object* v___x_1164_; lean_object* v_entries_1165_; lean_object* v_indexes_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1177_; 
v_fst_1163_ = lean_ctor_get(v_x_1162_, 0);
lean_inc(v_fst_1163_);
v___x_1164_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1160_, v_inst_1161_);
v_entries_1165_ = lean_ctor_get(v___x_1164_, 0);
v_indexes_1166_ = lean_ctor_get(v___x_1164_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1168_ = v___x_1164_;
v_isShared_1169_ = v_isSharedCheck_1177_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_indexes_1166_);
lean_inc(v_entries_1165_);
lean_dec(v___x_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1177_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_i_1170_; lean_object* v_f_1171_; lean_object* v_entries_1172_; lean_object* v_indexes_1173_; lean_object* v___x_1175_; 
v_i_1170_ = lean_array_get_size(v_entries_1165_);
v_f_1171_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1171_, 0, v_i_1170_);
v_entries_1172_ = lean_array_push(v_entries_1165_, v_x_1162_);
v_indexes_1173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1160_, v_inst_1161_, v_indexes_1166_, v_fst_1163_, v_f_1171_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v_indexes_1173_);
lean_ctor_set(v___x_1168_, 0, v_entries_1172_);
v___x_1175_ = v___x_1168_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_entries_1172_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_indexes_1173_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v___f_1180_; 
v___f_1180_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1180_, 0, v_inst_1178_);
lean_closure_set(v___f_1180_, 1, v_inst_1179_);
return v___f_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_){
_start:
{
lean_object* v___f_1187_; 
v___f_1187_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1187_, 0, v_inst_1183_);
lean_closure_set(v___f_1187_, 1, v_inst_1184_);
return v___f_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_x_1190_, lean_object* v_m_1191_){
_start:
{
lean_object* v_fst_1192_; lean_object* v_entries_1193_; lean_object* v_indexes_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1205_; 
v_fst_1192_ = lean_ctor_get(v_x_1190_, 0);
lean_inc(v_fst_1192_);
v_entries_1193_ = lean_ctor_get(v_m_1191_, 0);
v_indexes_1194_ = lean_ctor_get(v_m_1191_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_m_1191_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1196_ = v_m_1191_;
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_indexes_1194_);
lean_inc(v_entries_1193_);
lean_dec(v_m_1191_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1205_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_i_1198_; lean_object* v_f_1199_; lean_object* v_entries_1200_; lean_object* v_indexes_1201_; lean_object* v___x_1203_; 
v_i_1198_ = lean_array_get_size(v_entries_1193_);
v_f_1199_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1199_, 0, v_i_1198_);
v_entries_1200_ = lean_array_push(v_entries_1193_, v_x_1190_);
v_indexes_1201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1188_, v_inst_1189_, v_indexes_1194_, v_fst_1192_, v_f_1199_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v_indexes_1201_);
lean_ctor_set(v___x_1196_, 0, v_entries_1200_);
v___x_1203_ = v___x_1196_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_entries_1200_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_indexes_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___f_1208_; 
v___f_1208_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1208_, 0, v_inst_1206_);
lean_closure_set(v___f_1208_, 1, v_inst_1207_);
return v___f_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_inst_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v___f_1215_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1215_, 0, v_inst_1211_);
lean_closure_set(v___f_1215_, 1, v_inst_1212_);
return v___f_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1218_, 0, lean_box(0));
lean_closure_set(v___x_1218_, 1, lean_box(0));
lean_closure_set(v___x_1218_, 2, v_inst_1216_);
lean_closure_set(v___x_1218_, 3, v_inst_1217_);
lean_closure_set(v___x_1218_, 4, lean_box(0));
lean_closure_set(v___x_1218_, 5, lean_box(0));
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1225_, 0, lean_box(0));
lean_closure_set(v___x_1225_, 1, lean_box(0));
lean_closure_set(v___x_1225_, 2, v_inst_1221_);
lean_closure_set(v___x_1225_, 3, v_inst_1222_);
lean_closure_set(v___x_1225_, 4, lean_box(0));
lean_closure_set(v___x_1225_, 5, lean_box(0));
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1226_, lean_object* v_a_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_apply_2(v_f_1226_, v_a_1227_, v___y_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1231_, lean_object* v_00_u03b2_1232_, lean_object* v_map_1233_, lean_object* v_b_1234_, lean_object* v_f_1235_){
_start:
{
lean_object* v_entries_1236_; lean_object* v___f_1237_; size_t v_sz_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v_entries_1236_ = lean_ctor_get(v_map_1233_, 0);
lean_inc_ref(v_entries_1236_);
lean_dec_ref(v_map_1233_);
v___f_1237_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1237_, 0, v_f_1235_);
v_sz_1238_ = lean_array_size(v_entries_1236_);
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1231_, v_entries_1236_, v___f_1237_, v_sz_1238_, v___x_1239_, v_b_1234_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1241_){
_start:
{
lean_object* v___f_1242_; 
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1242_, 0, v_inst_1241_);
return v___f_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1243_, lean_object* v_00_u03b2_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_m_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v___f_1249_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1249_, 0, v_inst_1248_);
return v___f_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_, lean_object* v_m_1254_, lean_object* v_inst_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1250_, v_00_u03b2_1251_, v_inst_1252_, v_inst_1253_, v_m_1254_, v_inst_1255_);
lean_dec_ref(v_inst_1253_);
lean_dec_ref(v_inst_1252_);
return v_res_1256_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
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
res = runtime_initialize_Std_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_IndexMultiMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_IndexMultiMap(builtin);
}
#ifdef __cplusplus
}
#endif
