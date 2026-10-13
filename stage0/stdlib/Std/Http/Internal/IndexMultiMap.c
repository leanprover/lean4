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
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0_value;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2;
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_empty___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = lean_box(0);
v___x_181_ = lean_unsigned_to_nat(16u);
v___x_182_ = lean_mk_array(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__2);
v___x_187_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__0));
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg(){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___redArg___boxed(lean_object* v___dummy_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v_res_192_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_Internal_instInhabitedIndexMultiMap___redArg();
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_194_, lean_object* v_00_u03b2_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__0, &l_Std_Internal_instInhabitedIndexMultiMap___closed__0_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_201_, lean_object* v_00_u03b2_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_201_, v_00_u03b2_202_, v_inst_203_, v_inst_204_, v_inst_205_, v_inst_206_);
lean_dec(v_inst_206_);
lean_dec(v_inst_205_);
lean_dec_ref(v_inst_204_);
lean_dec_ref(v_inst_203_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___redArg___boxed(lean_object* v___dummy_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Internal_IndexMultiMap_instMembership___redArg();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_inst_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_217_, lean_object* v_00_u03b2_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_217_, v_00_u03b2_218_, v_inst_219_, v_inst_220_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_219_);
return v_res_221_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_key_224_, lean_object* v_map_225_){
_start:
{
lean_object* v_indexes_226_; uint8_t v___x_227_; 
v_indexes_226_ = lean_ctor_get(v_map_225_, 1);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_222_, v_inst_223_, v_indexes_226_, v_key_224_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_key_230_, lean_object* v_map_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_228_, v_inst_229_, v_key_230_, v_map_231_);
lean_dec_ref(v_map_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_key_238_, lean_object* v_map_239_){
_start:
{
uint8_t v___x_240_; 
v___x_240_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_236_, v_inst_237_, v_key_238_, v_map_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_inst_244_, lean_object* v_key_245_, lean_object* v_map_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_241_, v_00_u03b2_242_, v_inst_243_, v_inst_244_, v_key_245_, v_map_246_);
lean_dec_ref(v_map_246_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v___x_249_, lean_object* v_entries_250_, lean_object* v_x1_251_, lean_object* v_x2_252_, lean_object* v_x3_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_snd_256_; 
v___x_254_ = lean_array_fget_borrowed(v___x_249_, v_x1_251_);
v___x_255_ = lean_array_fget_borrowed(v_entries_250_, v___x_254_);
v_snd_256_ = lean_ctor_get(v___x_255_, 1);
lean_inc(v_snd_256_);
return v_snd_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v___x_257_, lean_object* v_entries_258_, lean_object* v_x1_259_, lean_object* v_x2_260_, lean_object* v_x3_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v___x_257_, v_entries_258_, v_x1_259_, v_x2_260_, v_x3_261_);
lean_dec(v_x2_260_);
lean_dec(v_x1_259_);
lean_dec_ref(v_entries_258_);
lean_dec(v___x_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_map_265_, lean_object* v_key_266_){
_start:
{
lean_object* v_entries_267_; lean_object* v_indexes_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; size_t v_sz_272_; size_t v___x_273_; lean_object* v_entries_274_; 
v_entries_267_ = lean_ctor_get(v_map_265_, 0);
lean_inc_ref(v_entries_267_);
v_indexes_268_ = lean_ctor_get(v_map_265_, 1);
lean_inc_ref(v_indexes_268_);
lean_dec_ref(v_map_265_);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_263_, v_inst_264_, v_indexes_268_, v_key_266_);
lean_dec_ref(v_indexes_268_);
lean_inc_n(v___x_269_, 2);
v___f_270_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_270_, 0, v___x_269_);
lean_closure_set(v___f_270_, 1, v_entries_267_);
v___x_271_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_272_ = lean_array_size(v___x_269_);
v___x_273_ = ((size_t)0ULL);
v_entries_274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_271_, v___x_269_, v___f_270_, v_sz_272_, v___x_273_, v___x_269_);
lean_dec(v___x_269_);
return v_entries_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_275_, lean_object* v_00_u03b2_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_map_279_, lean_object* v_key_280_, lean_object* v_h_281_){
_start:
{
lean_object* v_entries_282_; lean_object* v_indexes_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; size_t v_sz_287_; size_t v___x_288_; lean_object* v_entries_289_; 
v_entries_282_ = lean_ctor_get(v_map_279_, 0);
lean_inc_ref(v_entries_282_);
v_indexes_283_ = lean_ctor_get(v_map_279_, 1);
lean_inc_ref(v_indexes_283_);
lean_dec_ref(v_map_279_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_277_, v_inst_278_, v_indexes_283_, v_key_280_);
lean_dec_ref(v_indexes_283_);
lean_inc_n(v___x_284_, 2);
v___f_285_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_285_, 0, v___x_284_);
lean_closure_set(v___f_285_, 1, v_entries_282_);
v___x_286_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_287_ = lean_array_size(v___x_284_);
v___x_288_ = ((size_t)0ULL);
v_entries_289_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_286_, v___x_284_, v___f_285_, v_sz_287_, v___x_288_, v___x_284_);
lean_dec(v___x_284_);
return v_entries_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_map_292_, lean_object* v_key_293_){
_start:
{
lean_object* v_entries_294_; lean_object* v_indexes_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_entry_298_; lean_object* v___x_299_; lean_object* v_snd_300_; 
v_entries_294_ = lean_ctor_get(v_map_292_, 0);
v_indexes_295_ = lean_ctor_get(v_map_292_, 1);
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_290_, v_inst_291_, v_indexes_295_, v_key_293_);
v___x_297_ = lean_unsigned_to_nat(0u);
v_entry_298_ = lean_array_fget(v___x_296_, v___x_297_);
lean_dec(v___x_296_);
v___x_299_ = lean_array_fget_borrowed(v_entries_294_, v_entry_298_);
lean_dec(v_entry_298_);
v_snd_300_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_snd_300_);
return v_snd_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_map_303_, lean_object* v_key_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_301_, v_inst_302_, v_map_303_, v_key_304_);
lean_dec_ref(v_map_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_306_, lean_object* v_00_u03b2_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_map_310_, lean_object* v_key_311_, lean_object* v_h_312_){
_start:
{
lean_object* v_entries_313_; lean_object* v_indexes_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_entry_317_; lean_object* v___x_318_; lean_object* v_snd_319_; 
v_entries_313_ = lean_ctor_get(v_map_310_, 0);
v_indexes_314_ = lean_ctor_get(v_map_310_, 1);
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_308_, v_inst_309_, v_indexes_314_, v_key_311_);
v___x_316_ = lean_unsigned_to_nat(0u);
v_entry_317_ = lean_array_fget(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_array_fget_borrowed(v_entries_313_, v_entry_317_);
lean_dec(v_entry_317_);
v_snd_319_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_snd_319_);
return v_snd_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_map_324_, lean_object* v_key_325_, lean_object* v_h_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_320_, v_00_u03b2_321_, v_inst_322_, v_inst_323_, v_map_324_, v_key_325_, v_h_326_);
lean_dec_ref(v_map_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_map_330_, lean_object* v_key_331_){
_start:
{
lean_object* v_entries_332_; lean_object* v_indexes_333_; uint8_t v___x_334_; 
v_entries_332_ = lean_ctor_get(v_map_330_, 0);
lean_inc_ref(v_entries_332_);
v_indexes_333_ = lean_ctor_get(v_map_330_, 1);
lean_inc_ref(v_indexes_333_);
lean_dec_ref(v_map_330_);
lean_inc(v_key_331_);
lean_inc_ref(v_inst_329_);
lean_inc_ref(v_inst_328_);
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_328_, v_inst_329_, v_indexes_333_, v_key_331_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec_ref(v_indexes_333_);
lean_dec_ref(v_entries_332_);
lean_dec(v_key_331_);
lean_dec_ref(v_inst_329_);
lean_dec_ref(v_inst_328_);
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___f_337_; lean_object* v___x_338_; size_t v_sz_339_; size_t v___x_340_; lean_object* v_entries_341_; lean_object* v___x_342_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_328_, v_inst_329_, v_indexes_333_, v_key_331_);
lean_dec_ref(v_indexes_333_);
lean_inc_n(v___x_336_, 2);
v___f_337_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_337_, 0, v___x_336_);
lean_closure_set(v___f_337_, 1, v_entries_332_);
v___x_338_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_339_ = lean_array_size(v___x_336_);
v___x_340_ = ((size_t)0ULL);
v_entries_341_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_338_, v___x_336_, v___f_337_, v_sz_339_, v___x_340_, v___x_336_);
lean_dec(v___x_336_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_entries_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_map_347_, lean_object* v_key_348_){
_start:
{
lean_object* v_entries_349_; lean_object* v_indexes_350_; uint8_t v___x_351_; 
v_entries_349_ = lean_ctor_get(v_map_347_, 0);
lean_inc_ref(v_entries_349_);
v_indexes_350_ = lean_ctor_get(v_map_347_, 1);
lean_inc_ref(v_indexes_350_);
lean_dec_ref(v_map_347_);
lean_inc(v_key_348_);
lean_inc_ref(v_inst_346_);
lean_inc_ref(v_inst_345_);
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_345_, v_inst_346_, v_indexes_350_, v_key_348_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v_indexes_350_);
lean_dec_ref(v_entries_349_);
lean_dec(v_key_348_);
lean_dec_ref(v_inst_346_);
lean_dec_ref(v_inst_345_);
v___x_352_ = lean_box(0);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; size_t v_sz_356_; size_t v___x_357_; lean_object* v_entries_358_; lean_object* v___x_359_; 
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_345_, v_inst_346_, v_indexes_350_, v_key_348_);
lean_dec_ref(v_indexes_350_);
lean_inc_n(v___x_353_, 2);
v___f_354_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_354_, 0, v___x_353_);
lean_closure_set(v___f_354_, 1, v_entries_349_);
v___x_355_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_356_ = lean_array_size(v___x_353_);
v___x_357_ = ((size_t)0ULL);
v_entries_358_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_355_, v___x_353_, v___f_354_, v_sz_356_, v___x_357_, v___x_353_);
lean_dec(v___x_353_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_entries_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_map_362_, lean_object* v_key_363_){
_start:
{
lean_object* v_entries_364_; lean_object* v_indexes_365_; uint8_t v___x_366_; 
v_entries_364_ = lean_ctor_get(v_map_362_, 0);
v_indexes_365_ = lean_ctor_get(v_map_362_, 1);
lean_inc(v_key_363_);
lean_inc_ref(v_inst_361_);
lean_inc_ref(v_inst_360_);
v___x_366_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_360_, v_inst_361_, v_indexes_365_, v_key_363_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; 
lean_dec(v_key_363_);
lean_dec_ref(v_inst_361_);
lean_dec_ref(v_inst_360_);
v___x_367_ = lean_box(0);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_entry_370_; lean_object* v___x_371_; lean_object* v_snd_372_; lean_object* v___x_373_; 
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_360_, v_inst_361_, v_indexes_365_, v_key_363_);
v___x_369_ = lean_unsigned_to_nat(0u);
v_entry_370_ = lean_array_fget(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_array_fget_borrowed(v_entries_364_, v_entry_370_);
lean_dec(v_entry_370_);
v_snd_372_ = lean_ctor_get(v___x_371_, 1);
lean_inc(v_snd_372_);
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_snd_372_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_map_376_, lean_object* v_key_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_374_, v_inst_375_, v_map_376_, v_key_377_);
lean_dec_ref(v_map_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_map_383_, lean_object* v_key_384_){
_start:
{
lean_object* v_entries_385_; lean_object* v_indexes_386_; uint8_t v___x_387_; 
v_entries_385_ = lean_ctor_get(v_map_383_, 0);
v_indexes_386_ = lean_ctor_get(v_map_383_, 1);
lean_inc(v_key_384_);
lean_inc_ref(v_inst_382_);
lean_inc_ref(v_inst_381_);
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_381_, v_inst_382_, v_indexes_386_, v_key_384_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
lean_dec(v_key_384_);
lean_dec_ref(v_inst_382_);
lean_dec_ref(v_inst_381_);
v___x_388_ = lean_box(0);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_entry_391_; lean_object* v___x_392_; lean_object* v_snd_393_; lean_object* v___x_394_; 
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_381_, v_inst_382_, v_indexes_386_, v_key_384_);
v___x_390_ = lean_unsigned_to_nat(0u);
v_entry_391_ = lean_array_fget(v___x_389_, v___x_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_array_fget_borrowed(v_entries_385_, v_entry_391_);
lean_dec(v_entry_391_);
v_snd_393_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_393_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v_snd_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_395_, lean_object* v_00_u03b2_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_map_399_, lean_object* v_key_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_395_, v_00_u03b2_396_, v_inst_397_, v_inst_398_, v_map_399_, v_key_400_);
lean_dec_ref(v_map_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_402_, lean_object* v_value_403_, lean_object* v___x_404_, lean_object* v___x_405_, lean_object* v_a_406_, lean_object* v_x_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; 
lean_inc(v_a_406_);
v___x_409_ = lean_apply_2(v_inst_402_, v_a_406_, v_value_403_);
v___x_410_ = lean_unbox(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v_a_406_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_404_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___x_404_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_a_406_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_405_);
v___x_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_416_, lean_object* v_value_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_a_420_, lean_object* v_x_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_416_, v_value_417_, v___x_418_, v___x_419_, v_a_420_, v_x_421_, v___y_422_);
lean_dec_ref(v___y_422_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_map_429_, lean_object* v_inst_430_, lean_object* v_key_431_, lean_object* v_value_432_){
_start:
{
lean_object* v_entries_433_; lean_object* v_indexes_434_; uint8_t v___x_435_; 
v_entries_433_ = lean_ctor_get(v_map_429_, 0);
lean_inc_ref(v_entries_433_);
v_indexes_434_ = lean_ctor_get(v_map_429_, 1);
lean_inc_ref(v_indexes_434_);
lean_dec_ref(v_map_429_);
lean_inc(v_key_431_);
lean_inc_ref(v_inst_428_);
lean_inc_ref(v_inst_427_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_427_, v_inst_428_, v_indexes_434_, v_key_431_);
if (v___x_435_ == 0)
{
lean_dec_ref(v_indexes_434_);
lean_dec_ref(v_entries_433_);
lean_dec(v_value_432_);
lean_dec(v_key_431_);
lean_dec_ref(v_inst_430_);
lean_dec_ref(v_inst_428_);
lean_dec_ref(v_inst_427_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; size_t v_sz_439_; size_t v___x_440_; lean_object* v_entries_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___f_444_; size_t v_sz_445_; lean_object* v___x_446_; lean_object* v_fst_447_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_427_, v_inst_428_, v_indexes_434_, v_key_431_);
lean_dec_ref(v_indexes_434_);
lean_inc_n(v___x_436_, 2);
v___f_437_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_437_, 0, v___x_436_);
lean_closure_set(v___f_437_, 1, v_entries_433_);
v___x_438_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_439_ = lean_array_size(v___x_436_);
v___x_440_ = ((size_t)0ULL);
v_entries_441_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_438_, v___x_436_, v___f_437_, v_sz_439_, v___x_440_, v___x_436_);
lean_dec(v___x_436_);
v___x_442_ = lean_box(0);
v___x_443_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_444_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_444_, 0, v_inst_430_);
lean_closure_set(v___f_444_, 1, v_value_432_);
lean_closure_set(v___f_444_, 2, v___x_443_);
lean_closure_set(v___f_444_, 3, v___x_442_);
v_sz_445_ = lean_array_size(v_entries_441_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_438_, v_entries_441_, v___f_444_, v_sz_445_, v___x_440_, v___x_443_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
lean_dec(v___x_446_);
if (lean_obj_tag(v_fst_447_) == 0)
{
uint8_t v___x_448_; 
v___x_448_ = 0;
return v___x_448_;
}
else
{
lean_object* v_val_449_; 
v_val_449_ = lean_ctor_get(v_fst_447_, 0);
lean_inc(v_val_449_);
lean_dec_ref_known(v_fst_447_, 1);
if (lean_obj_tag(v_val_449_) == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 0;
return v___x_450_;
}
else
{
lean_dec_ref_known(v_val_449_, 1);
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_map_453_, lean_object* v_inst_454_, lean_object* v_key_455_, lean_object* v_value_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_451_, v_inst_452_, v_map_453_, v_inst_454_, v_key_455_, v_value_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_459_, lean_object* v_00_u03b2_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_map_463_, lean_object* v_inst_464_, lean_object* v_key_465_, lean_object* v_value_466_){
_start:
{
lean_object* v_entries_467_; lean_object* v_indexes_468_; uint8_t v___x_469_; 
v_entries_467_ = lean_ctor_get(v_map_463_, 0);
lean_inc_ref(v_entries_467_);
v_indexes_468_ = lean_ctor_get(v_map_463_, 1);
lean_inc_ref(v_indexes_468_);
lean_dec_ref(v_map_463_);
lean_inc(v_key_465_);
lean_inc_ref(v_inst_462_);
lean_inc_ref(v_inst_461_);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_461_, v_inst_462_, v_indexes_468_, v_key_465_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_indexes_468_);
lean_dec_ref(v_entries_467_);
lean_dec(v_value_466_);
lean_dec(v_key_465_);
lean_dec_ref(v_inst_464_);
lean_dec_ref(v_inst_462_);
lean_dec_ref(v_inst_461_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; size_t v_sz_473_; size_t v___x_474_; lean_object* v_entries_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___f_478_; size_t v_sz_479_; lean_object* v___x_480_; lean_object* v_fst_481_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_461_, v_inst_462_, v_indexes_468_, v_key_465_);
lean_dec_ref(v_indexes_468_);
lean_inc_n(v___x_470_, 2);
v___f_471_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_471_, 0, v___x_470_);
lean_closure_set(v___f_471_, 1, v_entries_467_);
v___x_472_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_473_ = lean_array_size(v___x_470_);
v___x_474_ = ((size_t)0ULL);
v_entries_475_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_472_, v___x_470_, v___f_471_, v_sz_473_, v___x_474_, v___x_470_);
lean_dec(v___x_470_);
v___x_476_ = lean_box(0);
v___x_477_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_478_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_478_, 0, v_inst_464_);
lean_closure_set(v___f_478_, 1, v_value_466_);
lean_closure_set(v___f_478_, 2, v___x_477_);
lean_closure_set(v___f_478_, 3, v___x_476_);
v_sz_479_ = lean_array_size(v_entries_475_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_472_, v_entries_475_, v___f_478_, v_sz_479_, v___x_474_, v___x_477_);
v_fst_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_fst_481_);
lean_dec(v___x_480_);
if (lean_obj_tag(v_fst_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 0;
return v___x_482_;
}
else
{
lean_object* v_val_483_; 
v_val_483_ = lean_ctor_get(v_fst_481_, 0);
lean_inc(v_val_483_);
lean_dec_ref_known(v_fst_481_, 1);
if (lean_obj_tag(v_val_483_) == 0)
{
uint8_t v___x_484_; 
v___x_484_ = 0;
return v___x_484_;
}
else
{
lean_dec_ref_known(v_val_483_, 1);
return v___x_469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_map_489_, lean_object* v_inst_490_, lean_object* v_key_491_, lean_object* v_value_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_485_, v_00_u03b2_486_, v_inst_487_, v_inst_488_, v_map_489_, v_inst_490_, v_key_491_, v_value_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_map_497_, lean_object* v_key_498_){
_start:
{
lean_object* v_entries_499_; lean_object* v_indexes_500_; uint8_t v___x_501_; 
v_entries_499_ = lean_ctor_get(v_map_497_, 0);
lean_inc_ref(v_entries_499_);
v_indexes_500_ = lean_ctor_get(v_map_497_, 1);
lean_inc_ref(v_indexes_500_);
lean_dec_ref(v_map_497_);
lean_inc(v_key_498_);
lean_inc_ref(v_inst_496_);
lean_inc_ref(v_inst_495_);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_495_, v_inst_496_, v_indexes_500_, v_key_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_indexes_500_);
lean_dec_ref(v_entries_499_);
lean_dec(v_key_498_);
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_inst_495_);
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___f_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v_entries_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_495_, v_inst_496_, v_indexes_500_, v_key_498_);
lean_dec_ref(v_indexes_500_);
lean_inc_n(v___x_503_, 2);
v___f_504_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_504_, 0, v___x_503_);
lean_closure_set(v___f_504_, 1, v_entries_499_);
v___x_505_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_506_ = lean_array_size(v___x_503_);
v___x_507_ = ((size_t)0ULL);
v_entries_508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_505_, v___x_503_, v___f_504_, v_sz_506_, v___x_507_, v___x_503_);
lean_dec(v___x_503_);
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
lean_object* v_entries_522_; lean_object* v_indexes_523_; uint8_t v___x_524_; 
v_entries_522_ = lean_ctor_get(v_map_520_, 0);
lean_inc_ref(v_entries_522_);
v_indexes_523_ = lean_ctor_get(v_map_520_, 1);
lean_inc_ref(v_indexes_523_);
lean_dec_ref(v_map_520_);
lean_inc(v_key_521_);
lean_inc_ref(v_inst_519_);
lean_inc_ref(v_inst_518_);
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_518_, v_inst_519_, v_indexes_523_, v_key_521_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_indexes_523_);
lean_dec_ref(v_entries_522_);
lean_dec(v_key_521_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
v___x_525_ = lean_box(0);
return v___x_525_;
}
else
{
lean_object* v___x_526_; lean_object* v___f_527_; lean_object* v___x_528_; size_t v_sz_529_; size_t v___x_530_; lean_object* v_entries_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_518_, v_inst_519_, v_indexes_523_, v_key_521_);
lean_dec_ref(v_indexes_523_);
lean_inc_n(v___x_526_, 2);
v___f_527_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_527_, 0, v___x_526_);
lean_closure_set(v___f_527_, 1, v_entries_522_);
v___x_528_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v_sz_529_ = lean_array_size(v___x_526_);
v___x_530_ = ((size_t)0ULL);
v_entries_531_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_528_, v___x_526_, v___f_527_, v_sz_529_, v___x_530_, v___x_526_);
lean_dec(v___x_526_);
v___x_532_ = lean_array_get_size(v_entries_531_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_sub(v___x_532_, v___x_533_);
v___x_535_ = lean_nat_dec_lt(v___x_534_, v___x_532_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
lean_dec(v___x_534_);
lean_dec(v_entries_531_);
v___x_536_ = lean_box(0);
return v___x_536_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_array_fget(v_entries_531_, v___x_534_);
lean_dec(v___x_534_);
lean_dec(v_entries_531_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_map_541_, lean_object* v_key_542_, lean_object* v_d_543_){
_start:
{
lean_object* v_entries_544_; lean_object* v_indexes_545_; uint8_t v___x_546_; 
v_entries_544_ = lean_ctor_get(v_map_541_, 0);
v_indexes_545_ = lean_ctor_get(v_map_541_, 1);
lean_inc(v_key_542_);
lean_inc_ref(v_inst_540_);
lean_inc_ref(v_inst_539_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_539_, v_inst_540_, v_indexes_545_, v_key_542_);
if (v___x_546_ == 0)
{
lean_dec(v_key_542_);
lean_dec_ref(v_inst_540_);
lean_dec_ref(v_inst_539_);
lean_inc(v_d_543_);
return v_d_543_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v_entry_549_; lean_object* v___x_550_; lean_object* v_snd_551_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_539_, v_inst_540_, v_indexes_545_, v_key_542_);
v___x_548_ = lean_unsigned_to_nat(0u);
v_entry_549_ = lean_array_fget(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_array_fget_borrowed(v_entries_544_, v_entry_549_);
lean_dec(v_entry_549_);
v_snd_551_ = lean_ctor_get(v___x_550_, 1);
lean_inc(v_snd_551_);
return v_snd_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_map_554_, lean_object* v_key_555_, lean_object* v_d_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_552_, v_inst_553_, v_map_554_, v_key_555_, v_d_556_);
lean_dec(v_d_556_);
lean_dec_ref(v_map_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_map_562_, lean_object* v_key_563_, lean_object* v_d_564_){
_start:
{
lean_object* v_entries_565_; lean_object* v_indexes_566_; uint8_t v___x_567_; 
v_entries_565_ = lean_ctor_get(v_map_562_, 0);
v_indexes_566_ = lean_ctor_get(v_map_562_, 1);
lean_inc(v_key_563_);
lean_inc_ref(v_inst_561_);
lean_inc_ref(v_inst_560_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_560_, v_inst_561_, v_indexes_566_, v_key_563_);
if (v___x_567_ == 0)
{
lean_dec(v_key_563_);
lean_dec_ref(v_inst_561_);
lean_dec_ref(v_inst_560_);
lean_inc(v_d_564_);
return v_d_564_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_entry_570_; lean_object* v___x_571_; lean_object* v_snd_572_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_560_, v_inst_561_, v_indexes_566_, v_key_563_);
v___x_569_ = lean_unsigned_to_nat(0u);
v_entry_570_ = lean_array_fget(v___x_568_, v___x_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_array_fget_borrowed(v_entries_565_, v_entry_570_);
lean_dec(v_entry_570_);
v_snd_572_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_572_);
return v_snd_572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_, lean_object* v_inst_576_, lean_object* v_map_577_, lean_object* v_key_578_, lean_object* v_d_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_573_, v_00_u03b2_574_, v_inst_575_, v_inst_576_, v_map_577_, v_key_578_, v_d_579_);
lean_dec(v_d_579_);
lean_dec_ref(v_map_577_);
return v_res_580_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_585_ = lean_unsigned_to_nat(14u);
v___x_586_ = lean_unsigned_to_nat(22u);
v___x_587_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_588_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_589_ = l_mkPanicMessageWithDecl(v___x_588_, v___x_587_, v___x_586_, v___x_585_, v___x_584_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_map_593_, lean_object* v_key_594_){
_start:
{
lean_object* v_entries_595_; lean_object* v_indexes_596_; uint8_t v___x_597_; 
v_entries_595_ = lean_ctor_get(v_map_593_, 0);
v_indexes_596_ = lean_ctor_get(v_map_593_, 1);
lean_inc(v_key_594_);
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_590_, v_inst_591_, v_indexes_596_, v_key_594_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_key_594_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_598_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_599_ = l_panic___redArg(v_inst_592_, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_entry_602_; lean_object* v___x_603_; lean_object* v_snd_604_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_590_, v_inst_591_, v_indexes_596_, v_key_594_);
v___x_601_ = lean_unsigned_to_nat(0u);
v_entry_602_ = lean_array_fget(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_fget_borrowed(v_entries_595_, v_entry_602_);
lean_dec(v_entry_602_);
v_snd_604_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_604_);
return v_snd_604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_605_, lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_map_608_, lean_object* v_key_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_605_, v_inst_606_, v_inst_607_, v_map_608_, v_key_609_);
lean_dec_ref(v_map_608_);
lean_dec(v_inst_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_611_, lean_object* v_00_u03b2_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_, lean_object* v_map_616_, lean_object* v_key_617_){
_start:
{
lean_object* v_entries_618_; lean_object* v_indexes_619_; uint8_t v___x_620_; 
v_entries_618_ = lean_ctor_get(v_map_616_, 0);
v_indexes_619_ = lean_ctor_get(v_map_616_, 1);
lean_inc(v_key_617_);
lean_inc_ref(v_inst_614_);
lean_inc_ref(v_inst_613_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_613_, v_inst_614_, v_indexes_619_, v_key_617_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_key_617_);
lean_dec_ref(v_inst_614_);
lean_dec_ref(v_inst_613_);
v___x_621_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_622_ = l_panic___redArg(v_inst_615_, v___x_621_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_entry_625_; lean_object* v___x_626_; lean_object* v_snd_627_; 
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_613_, v_inst_614_, v_indexes_619_, v_key_617_);
v___x_624_ = lean_unsigned_to_nat(0u);
v_entry_625_ = lean_array_fget(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_array_fget_borrowed(v_entries_618_, v_entry_625_);
lean_dec(v_entry_625_);
v_snd_627_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_627_);
return v_snd_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_map_633_, lean_object* v_key_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_628_, v_00_u03b2_629_, v_inst_630_, v_inst_631_, v_inst_632_, v_map_633_, v_key_634_);
lean_dec_ref(v_map_633_);
lean_dec(v_inst_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_636_, lean_object* v_h__1_637_, lean_object* v_h__2_638_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v_h__1_637_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_apply_1(v_h__2_638_, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_642_; 
lean_dec(v_h__2_638_);
v_val_641_ = lean_ctor_get(v_x_636_, 0);
lean_inc(v_val_641_);
lean_dec_ref_known(v_x_636_, 1);
v___x_642_ = lean_apply_1(v_h__1_637_, v_val_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_643_, lean_object* v_x_644_, lean_object* v_h__1_645_, lean_object* v_h__2_646_){
_start:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec(v_h__1_645_);
v___x_647_ = lean_box(0);
v___x_648_ = lean_apply_1(v_h__2_646_, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_val_649_; lean_object* v___x_650_; 
lean_dec(v_h__2_646_);
v_val_649_ = lean_ctor_get(v_x_644_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_x_644_, 1);
v___x_650_ = lean_apply_1(v_h__1_645_, v_val_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_mk_empty_array_with_capacity(v___x_653_);
v___x_655_ = lean_array_push(v___x_654_, v_i_651_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_val_657_ = lean_ctor_get(v_x_652_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_x_652_);
if (v_isSharedCheck_665_ == 0)
{
v___x_659_ = v_x_652_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_val_657_);
lean_dec(v_x_652_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_array_push(v_val_657_, v_i_651_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_666_, lean_object* v_inst_667_, lean_object* v_map_668_, lean_object* v_key_669_, lean_object* v_value_670_){
_start:
{
lean_object* v_entries_671_; lean_object* v_indexes_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_684_; 
v_entries_671_ = lean_ctor_get(v_map_668_, 0);
v_indexes_672_ = lean_ctor_get(v_map_668_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_map_668_);
if (v_isSharedCheck_684_ == 0)
{
v___x_674_ = v_map_668_;
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_indexes_672_);
lean_inc(v_entries_671_);
lean_dec(v_map_668_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_i_676_; lean_object* v_f_677_; lean_object* v___x_678_; lean_object* v_entries_679_; lean_object* v_indexes_680_; lean_object* v___x_682_; 
v_i_676_ = lean_array_get_size(v_entries_671_);
v_f_677_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_677_, 0, v_i_676_);
lean_inc(v_key_669_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_key_669_);
lean_ctor_set(v___x_678_, 1, v_value_670_);
v_entries_679_ = lean_array_push(v_entries_671_, v___x_678_);
v_indexes_680_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_666_, v_inst_667_, v_indexes_672_, v_key_669_, v_f_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v_indexes_680_);
lean_ctor_set(v___x_674_, 0, v_entries_679_);
v___x_682_ = v___x_674_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_entries_679_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_indexes_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_map_691_, lean_object* v_key_692_, lean_object* v_value_693_){
_start:
{
lean_object* v_entries_694_; lean_object* v_indexes_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_707_; 
v_entries_694_ = lean_ctor_get(v_map_691_, 0);
v_indexes_695_ = lean_ctor_get(v_map_691_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_map_691_);
if (v_isSharedCheck_707_ == 0)
{
v___x_697_ = v_map_691_;
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_indexes_695_);
lean_inc(v_entries_694_);
lean_dec(v_map_691_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_707_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_i_699_; lean_object* v_f_700_; lean_object* v___x_701_; lean_object* v_entries_702_; lean_object* v_indexes_703_; lean_object* v___x_705_; 
v_i_699_ = lean_array_get_size(v_entries_694_);
v_f_700_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_700_, 0, v_i_699_);
lean_inc(v_key_692_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_key_692_);
lean_ctor_set(v___x_701_, 1, v_value_693_);
v_entries_702_ = lean_array_push(v_entries_694_, v___x_701_);
v_indexes_703_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_687_, v_inst_688_, v_indexes_695_, v_key_692_, v_f_700_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_indexes_703_);
lean_ctor_set(v___x_697_, 0, v_entries_702_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_entries_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_indexes_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_708_, lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_x1_711_, lean_object* v_x2_712_){
_start:
{
lean_object* v_entries_713_; lean_object* v_indexes_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
v_entries_713_ = lean_ctor_get(v_x1_711_, 0);
v_indexes_714_ = lean_ctor_get(v_x1_711_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x1_711_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v_x1_711_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_indexes_714_);
lean_inc(v_entries_713_);
lean_dec(v_x1_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_i_718_; lean_object* v_f_719_; lean_object* v___x_720_; lean_object* v_entries_721_; lean_object* v_indexes_722_; lean_object* v___x_724_; 
v_i_718_ = lean_array_get_size(v_entries_713_);
v_f_719_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_719_, 0, v_i_718_);
lean_inc(v_key_708_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_key_708_);
lean_ctor_set(v___x_720_, 1, v_x2_712_);
v_entries_721_ = lean_array_push(v_entries_713_, v___x_720_);
v_indexes_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_709_, v_inst_710_, v_indexes_714_, v_key_708_, v_f_719_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_indexes_722_);
lean_ctor_set(v___x_716_, 0, v_entries_721_);
v___x_724_ = v___x_716_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_entries_721_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_indexes_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_map_729_, lean_object* v_key_730_, lean_object* v_values_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_array_get_size(v_values_731_);
v___x_734_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_735_ = lean_nat_dec_lt(v___x_732_, v___x_733_);
if (v___x_735_ == 0)
{
lean_dec_ref(v_values_731_);
lean_dec(v_key_730_);
lean_dec_ref(v_inst_728_);
lean_dec_ref(v_inst_727_);
return v_map_729_;
}
else
{
lean_object* v___f_736_; uint8_t v___x_737_; 
v___f_736_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_736_, 0, v_key_730_);
lean_closure_set(v___f_736_, 1, v_inst_727_);
lean_closure_set(v___f_736_, 2, v_inst_728_);
v___x_737_ = lean_nat_dec_le(v___x_733_, v___x_733_);
if (v___x_737_ == 0)
{
if (v___x_735_ == 0)
{
lean_dec_ref(v___f_736_);
lean_dec_ref(v_values_731_);
return v_map_729_;
}
else
{
size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; 
v___x_738_ = ((size_t)0ULL);
v___x_739_ = lean_usize_of_nat(v___x_733_);
v___x_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_734_, v___f_736_, v_values_731_, v___x_738_, v___x_739_, v_map_729_);
return v___x_740_;
}
}
else
{
size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v___x_741_ = ((size_t)0ULL);
v___x_742_ = lean_usize_of_nat(v___x_733_);
v___x_743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_734_, v___f_736_, v_values_731_, v___x_741_, v___x_742_, v_map_729_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_inst_749_, lean_object* v_map_750_, lean_object* v_key_751_, lean_object* v_values_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_values_752_);
v___x_755_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_756_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_756_ == 0)
{
lean_dec_ref(v_values_752_);
lean_dec(v_key_751_);
lean_dec_ref(v_inst_747_);
lean_dec_ref(v_inst_746_);
return v_map_750_;
}
else
{
lean_object* v___f_757_; uint8_t v___x_758_; 
v___f_757_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_757_, 0, v_key_751_);
lean_closure_set(v___f_757_, 1, v_inst_746_);
lean_closure_set(v___f_757_, 2, v_inst_747_);
v___x_758_ = lean_nat_dec_le(v___x_754_, v___x_754_);
if (v___x_758_ == 0)
{
if (v___x_756_ == 0)
{
lean_dec_ref(v___f_757_);
lean_dec_ref(v_values_752_);
return v_map_750_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_754_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_755_, v___f_757_, v_values_752_, v___x_759_, v___x_760_, v_map_750_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_754_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_755_, v___f_757_, v_values_752_, v___x_762_, v___x_763_, v_map_750_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg(){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___redArg___closed__3);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___redArg___boxed(lean_object* v___dummy_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v_res_768_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_empty___closed__0(void){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_Internal_IndexMultiMap_empty___redArg();
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_inst_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_inst_777_, lean_object* v_inst_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_775_, v_00_u03b2_776_, v_inst_777_, v_inst_778_);
lean_dec_ref(v_inst_778_);
lean_dec_ref(v_inst_777_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_acc_782_, lean_object* v_x_783_){
_start:
{
lean_object* v_fst_784_; lean_object* v_entries_785_; lean_object* v_indexes_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_797_; 
v_fst_784_ = lean_ctor_get(v_x_783_, 0);
lean_inc(v_fst_784_);
v_entries_785_ = lean_ctor_get(v_acc_782_, 0);
v_indexes_786_ = lean_ctor_get(v_acc_782_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_acc_782_);
if (v_isSharedCheck_797_ == 0)
{
v___x_788_ = v_acc_782_;
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_indexes_786_);
lean_inc(v_entries_785_);
lean_dec(v_acc_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v_i_790_; lean_object* v_f_791_; lean_object* v_entries_792_; lean_object* v_indexes_793_; lean_object* v___x_795_; 
v_i_790_ = lean_array_get_size(v_entries_785_);
v_f_791_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_791_, 0, v_i_790_);
v_entries_792_ = lean_array_push(v_entries_785_, v_x_783_);
v_indexes_793_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_780_, v_inst_781_, v_indexes_786_, v_fst_784_, v_f_791_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 1, v_indexes_793_);
lean_ctor_set(v___x_788_, 0, v_entries_792_);
v___x_795_ = v___x_788_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_entries_792_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_indexes_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_pairs_800_){
_start:
{
lean_object* v___f_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___f_801_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_801_, 0, v_inst_798_);
lean_closure_set(v___f_801_, 1, v_inst_799_);
v___x_802_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_803_ = l_List_foldl___redArg(v___f_801_, v___x_802_, v_pairs_800_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_pairs_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_806_, v_inst_807_, v_pairs_810_);
return v___x_811_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_map_814_, lean_object* v_key_815_){
_start:
{
lean_object* v_indexes_816_; uint8_t v___x_817_; 
v_indexes_816_ = lean_ctor_get(v_map_814_, 1);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_812_, v_inst_813_, v_indexes_816_, v_key_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_map_820_, lean_object* v_key_821_){
_start:
{
uint8_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_818_, v_inst_819_, v_map_820_, v_key_821_);
lean_dec_ref(v_map_820_);
v_r_823_ = lean_box(v_res_822_);
return v_r_823_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_824_, lean_object* v_00_u03b2_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_map_828_, lean_object* v_key_829_){
_start:
{
lean_object* v_indexes_830_; uint8_t v___x_831_; 
v_indexes_830_ = lean_ctor_get(v_map_828_, 1);
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_826_, v_inst_827_, v_indexes_830_, v_key_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_map_836_, lean_object* v_key_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_832_, v_00_u03b2_833_, v_inst_834_, v_inst_835_, v_map_836_, v_key_837_);
lean_dec_ref(v_map_836_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_key_842_, lean_object* v_f_843_, lean_object* v_x1_844_, lean_object* v_x2_845_){
_start:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_872_; 
v_fst_846_ = lean_ctor_get(v_x2_845_, 0);
v_snd_847_ = lean_ctor_get(v_x2_845_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_x2_845_);
if (v_isSharedCheck_872_ == 0)
{
v___x_849_ = v_x2_845_;
v_isShared_850_ = v_isSharedCheck_872_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_846_);
lean_dec(v_x2_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_872_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___y_852_; lean_object* v___x_869_; uint8_t v___x_870_; 
lean_inc_ref(v_inst_840_);
lean_inc(v_fst_846_);
v___x_869_ = lean_apply_2(v_inst_840_, v_fst_846_, v_key_842_);
v___x_870_ = lean_unbox(v___x_869_);
if (v___x_870_ == 0)
{
lean_dec(v_f_843_);
v___y_852_ = v_snd_847_;
goto v___jp_851_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = lean_apply_1(v_f_843_, v_snd_847_);
v___y_852_ = v___x_871_;
goto v___jp_851_;
}
v___jp_851_:
{
lean_object* v_entries_853_; lean_object* v_indexes_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_868_; 
v_entries_853_ = lean_ctor_get(v_x1_844_, 0);
v_indexes_854_ = lean_ctor_get(v_x1_844_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v_x1_844_);
if (v_isSharedCheck_868_ == 0)
{
v___x_856_ = v_x1_844_;
v_isShared_857_ = v_isSharedCheck_868_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_indexes_854_);
lean_inc(v_entries_853_);
lean_dec(v_x1_844_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_868_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_i_858_; lean_object* v_f_859_; lean_object* v___x_861_; 
v_i_858_ = lean_array_get_size(v_entries_853_);
v_f_859_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_859_, 0, v_i_858_);
lean_inc(v_fst_846_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___y_852_);
v___x_861_ = v___x_849_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___y_852_);
v___x_861_ = v_reuseFailAlloc_867_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v_entries_862_; lean_object* v_indexes_863_; lean_object* v___x_865_; 
v_entries_862_ = lean_array_push(v_entries_853_, v___x_861_);
v_indexes_863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_840_, v_inst_841_, v_indexes_854_, v_fst_846_, v_f_859_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 1, v_indexes_863_);
lean_ctor_set(v___x_856_, 0, v_entries_862_);
v___x_865_ = v___x_856_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_entries_862_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_indexes_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_map_875_, lean_object* v_key_876_, lean_object* v_f_877_){
_start:
{
uint8_t v___x_878_; 
lean_inc(v_key_876_);
lean_inc_ref(v_inst_874_);
lean_inc_ref(v_inst_873_);
v___x_878_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_873_, v_inst_874_, v_key_876_, v_map_875_);
if (v___x_878_ == 0)
{
lean_dec(v_f_877_);
lean_dec(v_key_876_);
lean_dec_ref(v_inst_874_);
lean_dec_ref(v_inst_873_);
return v_map_875_;
}
else
{
lean_object* v_entries_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_entries_879_ = lean_ctor_get(v_map_875_, 0);
lean_inc_ref(v_entries_879_);
lean_dec_ref(v_map_875_);
v___x_880_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = lean_array_get_size(v_entries_879_);
v___x_883_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_884_ = lean_nat_dec_lt(v___x_881_, v___x_882_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_entries_879_);
lean_dec(v_f_877_);
lean_dec(v_key_876_);
lean_dec_ref(v_inst_874_);
lean_dec_ref(v_inst_873_);
return v___x_880_;
}
else
{
lean_object* v___f_885_; uint8_t v___x_886_; 
v___f_885_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_885_, 0, v_inst_873_);
lean_closure_set(v___f_885_, 1, v_inst_874_);
lean_closure_set(v___f_885_, 2, v_key_876_);
lean_closure_set(v___f_885_, 3, v_f_877_);
v___x_886_ = lean_nat_dec_le(v___x_882_, v___x_882_);
if (v___x_886_ == 0)
{
if (v___x_884_ == 0)
{
lean_dec_ref(v___f_885_);
lean_dec_ref(v_entries_879_);
return v___x_880_;
}
else
{
size_t v___x_887_; size_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = ((size_t)0ULL);
v___x_888_ = lean_usize_of_nat(v___x_882_);
v___x_889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_883_, v___f_885_, v_entries_879_, v___x_887_, v___x_888_, v___x_880_);
return v___x_889_;
}
}
else
{
size_t v___x_890_; size_t v___x_891_; lean_object* v___x_892_; 
v___x_890_ = ((size_t)0ULL);
v___x_891_ = lean_usize_of_nat(v___x_882_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_883_, v___f_885_, v_entries_879_, v___x_890_, v___x_891_, v___x_880_);
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_map_899_, lean_object* v_key_900_, lean_object* v_f_901_){
_start:
{
uint8_t v___x_902_; 
lean_inc(v_key_900_);
lean_inc_ref(v_inst_896_);
lean_inc_ref(v_inst_895_);
v___x_902_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_895_, v_inst_896_, v_key_900_, v_map_899_);
if (v___x_902_ == 0)
{
lean_dec(v_f_901_);
lean_dec(v_key_900_);
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
return v_map_899_;
}
else
{
lean_object* v_entries_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_entries_903_ = lean_ctor_get(v_map_899_, 0);
lean_inc_ref(v_entries_903_);
lean_dec_ref(v_map_899_);
v___x_904_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_array_get_size(v_entries_903_);
v___x_907_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_908_ = lean_nat_dec_lt(v___x_905_, v___x_906_);
if (v___x_908_ == 0)
{
lean_dec_ref(v_entries_903_);
lean_dec(v_f_901_);
lean_dec(v_key_900_);
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
return v___x_904_;
}
else
{
lean_object* v___f_909_; uint8_t v___x_910_; 
v___f_909_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_909_, 0, v_inst_895_);
lean_closure_set(v___f_909_, 1, v_inst_896_);
lean_closure_set(v___f_909_, 2, v_key_900_);
lean_closure_set(v___f_909_, 3, v_f_901_);
v___x_910_ = lean_nat_dec_le(v___x_906_, v___x_906_);
if (v___x_910_ == 0)
{
if (v___x_908_ == 0)
{
lean_dec_ref(v___f_909_);
lean_dec_ref(v_entries_903_);
return v___x_904_;
}
else
{
size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((size_t)0ULL);
v___x_912_ = lean_usize_of_nat(v___x_906_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_907_, v___f_909_, v_entries_903_, v___x_911_, v___x_912_, v___x_904_);
return v___x_913_;
}
}
else
{
size_t v___x_914_; size_t v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((size_t)0ULL);
v___x_915_ = lean_usize_of_nat(v___x_906_);
v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_907_, v___f_909_, v_entries_903_, v___x_914_, v___x_915_, v___x_904_);
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_map_919_, lean_object* v_key_920_, lean_object* v_value_921_){
_start:
{
lean_object* v_entries_922_; lean_object* v_indexes_923_; uint8_t v___x_924_; 
v_entries_922_ = lean_ctor_get(v_map_919_, 0);
v_indexes_923_ = lean_ctor_get(v_map_919_, 1);
lean_inc(v_key_920_);
lean_inc_ref(v_inst_918_);
lean_inc_ref(v_inst_917_);
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_917_, v_inst_918_, v_indexes_923_, v_key_920_);
if (v___x_924_ == 0)
{
lean_dec(v_value_921_);
lean_dec(v_key_920_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v_inst_917_);
return v_map_919_;
}
else
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_938_; 
lean_inc_ref(v_indexes_923_);
lean_inc_ref(v_entries_922_);
v_isSharedCheck_938_ = !lean_is_exclusive(v_map_919_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; lean_object* v_unused_940_; 
v_unused_939_ = lean_ctor_get(v_map_919_, 1);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_map_919_, 0);
lean_dec(v_unused_940_);
v___x_926_ = v_map_919_;
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
else
{
lean_dec(v_map_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_938_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_idxs_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_lastIdx_932_; lean_object* v___x_933_; lean_object* v_entries_934_; lean_object* v___x_936_; 
lean_inc(v_key_920_);
v_idxs_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_917_, v_inst_918_, v_indexes_923_, v_key_920_);
v___x_929_ = lean_array_get_size(v_idxs_928_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v___x_929_, v___x_930_);
v_lastIdx_932_ = lean_array_fget(v_idxs_928_, v___x_931_);
lean_dec(v___x_931_);
lean_dec(v_idxs_928_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v_key_920_);
lean_ctor_set(v___x_933_, 1, v_value_921_);
v_entries_934_ = lean_array_fset(v_entries_922_, v_lastIdx_932_, v___x_933_);
lean_dec(v_lastIdx_932_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v_entries_934_);
v___x_936_ = v___x_926_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_entries_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_indexes_923_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_map_945_, lean_object* v_key_946_, lean_object* v_value_947_){
_start:
{
lean_object* v_entries_948_; lean_object* v_indexes_949_; uint8_t v___x_950_; 
v_entries_948_ = lean_ctor_get(v_map_945_, 0);
v_indexes_949_ = lean_ctor_get(v_map_945_, 1);
lean_inc(v_key_946_);
lean_inc_ref(v_inst_944_);
lean_inc_ref(v_inst_943_);
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_943_, v_inst_944_, v_indexes_949_, v_key_946_);
if (v___x_950_ == 0)
{
lean_dec(v_value_947_);
lean_dec(v_key_946_);
lean_dec_ref(v_inst_944_);
lean_dec_ref(v_inst_943_);
return v_map_945_;
}
else
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_964_; 
lean_inc_ref(v_indexes_949_);
lean_inc_ref(v_entries_948_);
v_isSharedCheck_964_ = !lean_is_exclusive(v_map_945_);
if (v_isSharedCheck_964_ == 0)
{
lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_965_ = lean_ctor_get(v_map_945_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_map_945_, 0);
lean_dec(v_unused_966_);
v___x_952_ = v_map_945_;
v_isShared_953_ = v_isSharedCheck_964_;
goto v_resetjp_951_;
}
else
{
lean_dec(v_map_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_964_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_idxs_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_lastIdx_958_; lean_object* v___x_959_; lean_object* v_entries_960_; lean_object* v___x_962_; 
lean_inc(v_key_946_);
v_idxs_954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_943_, v_inst_944_, v_indexes_949_, v_key_946_);
v___x_955_ = lean_array_get_size(v_idxs_954_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_sub(v___x_955_, v___x_956_);
v_lastIdx_958_ = lean_array_fget(v_idxs_954_, v___x_957_);
lean_dec(v___x_957_);
lean_dec(v_idxs_954_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_key_946_);
lean_ctor_set(v___x_959_, 1, v_value_947_);
v_entries_960_ = lean_array_fset(v_entries_948_, v_lastIdx_958_, v___x_959_);
lean_dec(v_lastIdx_958_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_entries_960_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_entries_960_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_indexes_949_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_967_, lean_object* v_key_968_, lean_object* v_inst_969_, lean_object* v_x1_970_, lean_object* v_x2_971_){
_start:
{
lean_object* v_fst_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_fst_972_ = lean_ctor_get(v_x2_971_, 0);
lean_inc_n(v_fst_972_, 2);
lean_inc_ref(v_inst_967_);
v___x_973_ = lean_apply_2(v_inst_967_, v_key_968_, v_fst_972_);
v___x_974_ = lean_unbox(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v_entries_975_; lean_object* v_indexes_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_987_; 
v_entries_975_ = lean_ctor_get(v_x1_970_, 0);
v_indexes_976_ = lean_ctor_get(v_x1_970_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_x1_970_);
if (v_isSharedCheck_987_ == 0)
{
v___x_978_ = v_x1_970_;
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_indexes_976_);
lean_inc(v_entries_975_);
lean_dec(v_x1_970_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_i_980_; lean_object* v_f_981_; lean_object* v_entries_982_; lean_object* v_indexes_983_; lean_object* v___x_985_; 
v_i_980_ = lean_array_get_size(v_entries_975_);
v_f_981_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_981_, 0, v_i_980_);
v_entries_982_ = lean_array_push(v_entries_975_, v_x2_971_);
v_indexes_983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_967_, v_inst_969_, v_indexes_976_, v_fst_972_, v_f_981_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v_indexes_983_);
lean_ctor_set(v___x_978_, 0, v_entries_982_);
v___x_985_ = v___x_978_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_entries_982_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_indexes_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_dec(v_fst_972_);
lean_dec_ref(v_x2_971_);
lean_dec_ref(v_inst_969_);
lean_dec_ref(v_inst_967_);
return v_x1_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_map_990_, lean_object* v_key_991_){
_start:
{
uint8_t v___x_992_; 
lean_inc(v_key_991_);
lean_inc_ref(v_inst_989_);
lean_inc_ref(v_inst_988_);
v___x_992_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_988_, v_inst_989_, v_key_991_, v_map_990_);
if (v___x_992_ == 0)
{
lean_dec(v_key_991_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
return v_map_990_;
}
else
{
lean_object* v_entries_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_entries_993_ = lean_ctor_get(v_map_990_, 0);
lean_inc_ref(v_entries_993_);
lean_dec_ref(v_map_990_);
v___x_994_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_array_get_size(v_entries_993_);
v___x_997_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_998_ = lean_nat_dec_lt(v___x_995_, v___x_996_);
if (v___x_998_ == 0)
{
lean_dec_ref(v_entries_993_);
lean_dec(v_key_991_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
return v___x_994_;
}
else
{
lean_object* v___f_999_; uint8_t v___x_1000_; 
v___f_999_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_999_, 0, v_inst_988_);
lean_closure_set(v___f_999_, 1, v_key_991_);
lean_closure_set(v___f_999_, 2, v_inst_989_);
v___x_1000_ = lean_nat_dec_le(v___x_996_, v___x_996_);
if (v___x_1000_ == 0)
{
if (v___x_998_ == 0)
{
lean_dec_ref(v___f_999_);
lean_dec_ref(v_entries_993_);
return v___x_994_;
}
else
{
size_t v___x_1001_; size_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = lean_usize_of_nat(v___x_996_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_997_, v___f_999_, v_entries_993_, v___x_1001_, v___x_1002_, v___x_994_);
return v___x_1003_;
}
}
else
{
size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_996_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_997_, v___f_999_, v_entries_993_, v___x_1004_, v___x_1005_, v___x_994_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_inst_1012_, lean_object* v_map_1013_, lean_object* v_key_1014_){
_start:
{
uint8_t v___x_1015_; 
lean_inc(v_key_1014_);
lean_inc_ref(v_inst_1010_);
lean_inc_ref(v_inst_1009_);
v___x_1015_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1009_, v_inst_1010_, v_key_1014_, v_map_1013_);
if (v___x_1015_ == 0)
{
lean_dec(v_key_1014_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
return v_map_1013_;
}
else
{
lean_object* v_entries_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_entries_1016_ = lean_ctor_get(v_map_1013_, 0);
lean_inc_ref(v_entries_1016_);
lean_dec_ref(v_map_1013_);
v___x_1017_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_array_get_size(v_entries_1016_);
v___x_1020_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1021_ = lean_nat_dec_lt(v___x_1018_, v___x_1019_);
if (v___x_1021_ == 0)
{
lean_dec_ref(v_entries_1016_);
lean_dec(v_key_1014_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
return v___x_1017_;
}
else
{
lean_object* v___f_1022_; uint8_t v___x_1023_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1022_, 0, v_inst_1009_);
lean_closure_set(v___f_1022_, 1, v_key_1014_);
lean_closure_set(v___f_1022_, 2, v_inst_1010_);
v___x_1023_ = lean_nat_dec_le(v___x_1019_, v___x_1019_);
if (v___x_1023_ == 0)
{
if (v___x_1021_ == 0)
{
lean_dec_ref(v___f_1022_);
lean_dec_ref(v_entries_1016_);
return v___x_1017_;
}
else
{
size_t v___x_1024_; size_t v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((size_t)0ULL);
v___x_1025_ = lean_usize_of_nat(v___x_1019_);
v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1020_, v___f_1022_, v_entries_1016_, v___x_1024_, v___x_1025_, v___x_1017_);
return v___x_1026_;
}
}
else
{
size_t v___x_1027_; size_t v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = lean_usize_of_nat(v___x_1019_);
v___x_1029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1020_, v___f_1022_, v_entries_1016_, v___x_1027_, v___x_1028_, v___x_1017_);
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object* v_inst_1030_, lean_object* v_keys_1031_, lean_object* v_inst_1032_, lean_object* v_x1_1033_, lean_object* v_x2_1034_){
_start:
{
lean_object* v_fst_1035_; uint8_t v___x_1036_; 
v_fst_1035_ = lean_ctor_get(v_x2_1034_, 0);
lean_inc_n(v_fst_1035_, 2);
lean_inc_ref(v_inst_1030_);
v___x_1036_ = l_Array_contains___redArg(v_inst_1030_, v_keys_1031_, v_fst_1035_);
if (v___x_1036_ == 0)
{
lean_object* v_entries_1037_; lean_object* v_indexes_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_entries_1037_ = lean_ctor_get(v_x1_1033_, 0);
v_indexes_1038_ = lean_ctor_get(v_x1_1033_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x1_1033_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1040_ = v_x1_1033_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_indexes_1038_);
lean_inc(v_entries_1037_);
lean_dec(v_x1_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_i_1042_; lean_object* v_f_1043_; lean_object* v_entries_1044_; lean_object* v_indexes_1045_; lean_object* v___x_1047_; 
v_i_1042_ = lean_array_get_size(v_entries_1037_);
v_f_1043_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1043_, 0, v_i_1042_);
v_entries_1044_ = lean_array_push(v_entries_1037_, v_x2_1034_);
v_indexes_1045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1030_, v_inst_1032_, v_indexes_1038_, v_fst_1035_, v_f_1043_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v_indexes_1045_);
lean_ctor_set(v___x_1040_, 0, v_entries_1044_);
v___x_1047_ = v___x_1040_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_entries_1044_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_indexes_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
else
{
lean_dec(v_fst_1035_);
lean_dec_ref(v_x2_1034_);
lean_dec_ref(v_inst_1032_);
lean_dec_ref(v_inst_1030_);
return v_x1_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_map_1052_, lean_object* v_keys_1053_){
_start:
{
lean_object* v_entries_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_entries_1054_ = lean_ctor_get(v_map_1052_, 0);
lean_inc_ref(v_entries_1054_);
lean_dec_ref(v_map_1052_);
v___x_1055_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_array_get_size(v_entries_1054_);
v___x_1058_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1059_ = lean_nat_dec_lt(v___x_1056_, v___x_1057_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v_entries_1054_);
lean_dec_ref(v_keys_1053_);
lean_dec_ref(v_inst_1051_);
lean_dec_ref(v_inst_1050_);
return v___x_1055_;
}
else
{
lean_object* v___f_1060_; uint8_t v___x_1061_; 
v___f_1060_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1060_, 0, v_inst_1050_);
lean_closure_set(v___f_1060_, 1, v_keys_1053_);
lean_closure_set(v___f_1060_, 2, v_inst_1051_);
v___x_1061_ = lean_nat_dec_le(v___x_1057_, v___x_1057_);
if (v___x_1061_ == 0)
{
if (v___x_1059_ == 0)
{
lean_dec_ref(v___f_1060_);
lean_dec_ref(v_entries_1054_);
return v___x_1055_;
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1057_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1058_, v___f_1060_, v_entries_1054_, v___x_1062_, v___x_1063_, v___x_1055_);
return v___x_1064_;
}
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1057_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1058_, v___f_1060_, v_entries_1054_, v___x_1065_, v___x_1066_, v___x_1055_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object* v_00_u03b1_1068_, lean_object* v_00_u03b2_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_map_1074_, lean_object* v_keys_1075_){
_start:
{
lean_object* v_entries_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v_entries_1076_ = lean_ctor_get(v_map_1074_, 0);
lean_inc_ref(v_entries_1076_);
lean_dec_ref(v_map_1074_);
v___x_1077_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = lean_array_get_size(v_entries_1076_);
v___x_1080_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1081_ = lean_nat_dec_lt(v___x_1078_, v___x_1079_);
if (v___x_1081_ == 0)
{
lean_dec_ref(v_entries_1076_);
lean_dec_ref(v_keys_1075_);
lean_dec_ref(v_inst_1071_);
lean_dec_ref(v_inst_1070_);
return v___x_1077_;
}
else
{
lean_object* v___f_1082_; uint8_t v___x_1083_; 
v___f_1082_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1082_, 0, v_inst_1070_);
lean_closure_set(v___f_1082_, 1, v_keys_1075_);
lean_closure_set(v___f_1082_, 2, v_inst_1071_);
v___x_1083_ = lean_nat_dec_le(v___x_1079_, v___x_1079_);
if (v___x_1083_ == 0)
{
if (v___x_1081_ == 0)
{
lean_dec_ref(v___f_1082_);
lean_dec_ref(v_entries_1076_);
return v___x_1077_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1079_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1080_, v___f_1082_, v_entries_1076_, v___x_1084_, v___x_1085_, v___x_1077_);
return v___x_1086_;
}
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1079_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1080_, v___f_1082_, v_entries_1076_, v___x_1087_, v___x_1088_, v___x_1077_);
return v___x_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1090_){
_start:
{
lean_object* v_entries_1091_; lean_object* v___x_1092_; 
v_entries_1091_ = lean_ctor_get(v_map_1090_, 0);
v___x_1092_ = lean_array_get_size(v_entries_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1093_);
lean_dec_ref(v_map_1093_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_map_1099_){
_start:
{
lean_object* v_entries_1100_; lean_object* v___x_1101_; 
v_entries_1100_ = lean_ctor_get(v_map_1099_, 0);
v___x_1101_ = lean_array_get_size(v_entries_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1102_, lean_object* v_00_u03b2_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_map_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1102_, v_00_u03b2_1103_, v_inst_1104_, v_inst_1105_, v_map_1106_);
lean_dec_ref(v_map_1106_);
lean_dec_ref(v_inst_1105_);
lean_dec_ref(v_inst_1104_);
return v_res_1107_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1108_){
_start:
{
lean_object* v_entries_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_entries_1109_ = lean_ctor_get(v_map_1108_, 0);
v___x_1110_ = lean_array_get_size(v_entries_1109_);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_nat_dec_eq(v___x_1110_, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1113_){
_start:
{
uint8_t v_res_1114_; lean_object* v_r_1115_; 
v_res_1114_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1113_);
lean_dec_ref(v_map_1113_);
v_r_1115_ = lean_box(v_res_1114_);
return v_r_1115_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_map_1120_){
_start:
{
lean_object* v_entries_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v_entries_1121_ = lean_ctor_get(v_map_1120_, 0);
v___x_1122_ = lean_array_get_size(v_entries_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_eq(v___x_1122_, v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v_map_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1125_, v_00_u03b2_1126_, v_inst_1127_, v_inst_1128_, v_map_1129_);
lean_dec_ref(v_map_1129_);
lean_dec_ref(v_inst_1128_);
lean_dec_ref(v_inst_1127_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1132_){
_start:
{
lean_object* v_entries_1133_; 
v_entries_1133_ = lean_ctor_get(v_map_1132_, 0);
lean_inc_ref(v_entries_1133_);
return v_entries_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1134_);
lean_dec_ref(v_map_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_map_1140_){
_start:
{
lean_object* v_entries_1141_; 
v_entries_1141_ = lean_ctor_get(v_map_1140_, 0);
lean_inc_ref(v_entries_1141_);
return v_entries_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_00_u03b2_1143_, lean_object* v_inst_1144_, lean_object* v_inst_1145_, lean_object* v_map_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1142_, v_00_u03b2_1143_, v_inst_1144_, v_inst_1145_, v_map_1146_);
lean_dec_ref(v_map_1146_);
lean_dec_ref(v_inst_1145_);
lean_dec_ref(v_inst_1144_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1148_){
_start:
{
lean_object* v_entries_1149_; lean_object* v___x_1150_; 
v_entries_1149_ = lean_ctor_get(v_map_1148_, 0);
lean_inc_ref(v_entries_1149_);
lean_dec_ref(v_map_1148_);
v___x_1150_ = lean_array_to_list(v_entries_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_map_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_map_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1157_, v_00_u03b2_1158_, v_inst_1159_, v_inst_1160_, v_map_1161_);
lean_dec_ref(v_inst_1160_);
lean_dec_ref(v_inst_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_x1_1165_, lean_object* v_x2_1166_){
_start:
{
lean_object* v_fst_1167_; lean_object* v_entries_1168_; lean_object* v_indexes_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1180_; 
v_fst_1167_ = lean_ctor_get(v_x2_1166_, 0);
lean_inc(v_fst_1167_);
v_entries_1168_ = lean_ctor_get(v_x1_1165_, 0);
v_indexes_1169_ = lean_ctor_get(v_x1_1165_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_x1_1165_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1171_ = v_x1_1165_;
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_indexes_1169_);
lean_inc(v_entries_1168_);
lean_dec(v_x1_1165_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1180_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_i_1173_; lean_object* v_f_1174_; lean_object* v_entries_1175_; lean_object* v_indexes_1176_; lean_object* v___x_1178_; 
v_i_1173_ = lean_array_get_size(v_entries_1168_);
v_f_1174_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1174_, 0, v_i_1173_);
v_entries_1175_ = lean_array_push(v_entries_1168_, v_x2_1166_);
v_indexes_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1163_, v_inst_1164_, v_indexes_1169_, v_fst_1167_, v_f_1174_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v_indexes_1176_);
lean_ctor_set(v___x_1171_, 0, v_entries_1175_);
v___x_1178_ = v___x_1171_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_entries_1175_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_indexes_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_m1_1183_, lean_object* v_m2_1184_){
_start:
{
lean_object* v_entries_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_entries_1185_ = lean_ctor_get(v_m2_1184_, 0);
lean_inc_ref(v_entries_1185_);
lean_dec_ref(v_m2_1184_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_array_get_size(v_entries_1185_);
v___x_1188_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_1189_ = lean_nat_dec_lt(v___x_1186_, v___x_1187_);
if (v___x_1189_ == 0)
{
lean_dec_ref(v_entries_1185_);
lean_dec_ref(v_inst_1182_);
lean_dec_ref(v_inst_1181_);
return v_m1_1183_;
}
else
{
lean_object* v___f_1190_; uint8_t v___x_1191_; 
v___f_1190_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1190_, 0, v_inst_1181_);
lean_closure_set(v___f_1190_, 1, v_inst_1182_);
v___x_1191_ = lean_nat_dec_le(v___x_1187_, v___x_1187_);
if (v___x_1191_ == 0)
{
if (v___x_1189_ == 0)
{
lean_dec_ref(v___f_1190_);
lean_dec_ref(v_entries_1185_);
return v_m1_1183_;
}
else
{
size_t v___x_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = ((size_t)0ULL);
v___x_1193_ = lean_usize_of_nat(v___x_1187_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1188_, v___f_1190_, v_entries_1185_, v___x_1192_, v___x_1193_, v_m1_1183_);
return v___x_1194_;
}
}
else
{
size_t v___x_1195_; size_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = lean_usize_of_nat(v___x_1187_);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1188_, v___f_1190_, v_entries_1185_, v___x_1195_, v___x_1196_, v_m1_1183_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m1_1204_, lean_object* v_m2_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1200_, v_inst_1201_, v_m1_1204_, v_m2_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg();
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1211_, lean_object* v_00_u03b2_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1216_, v_00_u03b2_1217_, v_inst_1218_, v_inst_1219_);
lean_dec_ref(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1221_, lean_object* v_inst_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_fst_1224_; lean_object* v___x_1225_; lean_object* v_entries_1226_; lean_object* v_indexes_1227_; lean_object* v_i_1228_; lean_object* v_f_1229_; lean_object* v_entries_1230_; lean_object* v_indexes_1231_; lean_object* v___x_1232_; 
v_fst_1224_ = lean_ctor_get(v_x_1223_, 0);
lean_inc(v_fst_1224_);
v___x_1225_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_empty___closed__0, &l_Std_Internal_IndexMultiMap_empty___closed__0_once, _init_l_Std_Internal_IndexMultiMap_empty___closed__0);
v_entries_1226_ = lean_ctor_get(v___x_1225_, 0);
v_indexes_1227_ = lean_ctor_get(v___x_1225_, 1);
v_i_1228_ = lean_array_get_size(v_entries_1226_);
v_f_1229_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1229_, 0, v_i_1228_);
lean_inc_ref(v_entries_1226_);
v_entries_1230_ = lean_array_push(v_entries_1226_, v_x_1223_);
lean_inc_ref(v_indexes_1227_);
v_indexes_1231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1221_, v_inst_1222_, v_indexes_1227_, v_fst_1224_, v_f_1229_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_entries_1230_);
lean_ctor_set(v___x_1232_, 1, v_indexes_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1233_, lean_object* v_inst_1234_){
_start:
{
lean_object* v___f_1235_; 
v___f_1235_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1235_, 0, v_inst_1233_);
lean_closure_set(v___f_1235_, 1, v_inst_1234_);
return v___f_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_){
_start:
{
lean_object* v___f_1242_; 
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1242_, 0, v_inst_1238_);
lean_closure_set(v___f_1242_, 1, v_inst_1239_);
return v___f_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_x_1245_, lean_object* v_m_1246_){
_start:
{
lean_object* v_fst_1247_; lean_object* v_entries_1248_; lean_object* v_indexes_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1260_; 
v_fst_1247_ = lean_ctor_get(v_x_1245_, 0);
lean_inc(v_fst_1247_);
v_entries_1248_ = lean_ctor_get(v_m_1246_, 0);
v_indexes_1249_ = lean_ctor_get(v_m_1246_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_m_1246_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1251_ = v_m_1246_;
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_indexes_1249_);
lean_inc(v_entries_1248_);
lean_dec(v_m_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_i_1253_; lean_object* v_f_1254_; lean_object* v_entries_1255_; lean_object* v_indexes_1256_; lean_object* v___x_1258_; 
v_i_1253_ = lean_array_get_size(v_entries_1248_);
v_f_1254_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insert___redArg___lam__0), 2, 1);
lean_closure_set(v_f_1254_, 0, v_i_1253_);
v_entries_1255_ = lean_array_push(v_entries_1248_, v_x_1245_);
v_indexes_1256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1243_, v_inst_1244_, v_indexes_1249_, v_fst_1247_, v_f_1254_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_indexes_1256_);
lean_ctor_set(v___x_1251_, 0, v_entries_1255_);
v___x_1258_ = v___x_1251_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_entries_1255_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_indexes_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1261_, lean_object* v_inst_1262_){
_start:
{
lean_object* v___f_1263_; 
v___f_1263_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1263_, 0, v_inst_1261_);
lean_closure_set(v___f_1263_, 1, v_inst_1262_);
return v___f_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_inst_1269_){
_start:
{
lean_object* v___f_1270_; 
v___f_1270_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1270_, 0, v_inst_1266_);
lean_closure_set(v___f_1270_, 1, v_inst_1267_);
return v___f_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_1271_, lean_object* v_inst_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1273_, 0, lean_box(0));
lean_closure_set(v___x_1273_, 1, lean_box(0));
lean_closure_set(v___x_1273_, 2, v_inst_1271_);
lean_closure_set(v___x_1273_, 3, v_inst_1272_);
lean_closure_set(v___x_1273_, 4, lean_box(0));
lean_closure_set(v___x_1273_, 5, lean_box(0));
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_1280_, 0, lean_box(0));
lean_closure_set(v___x_1280_, 1, lean_box(0));
lean_closure_set(v___x_1280_, 2, v_inst_1276_);
lean_closure_set(v___x_1280_, 3, v_inst_1277_);
lean_closure_set(v___x_1280_, 4, lean_box(0));
lean_closure_set(v___x_1280_, 5, lean_box(0));
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1281_, lean_object* v_a_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_apply_2(v_f_1281_, v_a_1282_, v___y_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1286_, lean_object* v_00_u03b2_1287_, lean_object* v_map_1288_, lean_object* v_b_1289_, lean_object* v_f_1290_){
_start:
{
lean_object* v_entries_1291_; lean_object* v___f_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v_entries_1291_ = lean_ctor_get(v_map_1288_, 0);
lean_inc_ref(v_entries_1291_);
lean_dec_ref(v_map_1288_);
v___f_1292_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1292_, 0, v_f_1290_);
v_sz_1293_ = lean_array_size(v_entries_1291_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1286_, v_entries_1291_, v___f_1292_, v_sz_1293_, v___x_1294_, v_b_1289_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_1296_){
_start:
{
lean_object* v___f_1297_; 
v___f_1297_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1297_, 0, v_inst_1296_);
return v___f_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_1298_, lean_object* v_00_u03b2_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_m_1302_, lean_object* v_inst_1303_){
_start:
{
lean_object* v___f_1304_; 
v___f_1304_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1304_, 0, v_inst_1303_);
return v___f_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_00_u03b2_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_m_1309_, lean_object* v_inst_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_1305_, v_00_u03b2_1306_, v_inst_1307_, v_inst_1308_, v_m_1309_, v_inst_1310_);
lean_dec_ref(v_inst_1308_);
lean_dec_ref(v_inst_1307_);
return v_res_1311_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_IndexMultiMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
