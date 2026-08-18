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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instRepr___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__1_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entries"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__6_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__11_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "indexes"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__13_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__2_value)} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__16_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value;
static const lean_closure_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__18_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__19_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__25_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__20_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__21_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__22_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__23_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__26_value),((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__24_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "validity"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__28_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__30_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31_value;
static const lean_string_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_value;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33;
static lean_once_cell_t l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35_value;
static const lean_ctor_object l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__32_value)}};
static const lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36 = (const lean_object*)&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36_value;
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
static lean_once_cell_t l_Std_Internal_instInhabitedIndexMultiMap___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_instInhabitedIndexMultiMap___closed__4;
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
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0;
static lean_once_cell_t l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1;
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
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg___lam__0(lean_object* v_x1_1_, lean_object* v_x2_2_, lean_object* v_x3_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_x2_2_);
lean_ctor_set(v___x_4_, 1, v_x3_3_);
v___x_5_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_x1_1_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(11u);
v___x_24_ = lean_nat_to_int(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__3));
v___x_63_ = lean_string_length(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__33);
v___x_65_ = lean_nat_to_int(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___redArg(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_entries_73_; lean_object* v_indexes_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_125_; 
v_entries_73_ = lean_ctor_get(v_x_72_, 0);
v_indexes_74_ = lean_ctor_get(v_x_72_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_72_);
if (v_isSharedCheck_125_ == 0)
{
v___x_76_ = v_x_72_;
v_isShared_77_ = v_isSharedCheck_125_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_indexes_74_);
lean_inc(v_entries_73_);
lean_dec(v_x_72_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_125_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___f_78_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__0));
v___x_79_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__8));
v___x_80_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__9));
v___x_81_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__10);
v___f_82_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_82_, 0, v_inst_71_);
lean_inc_ref(v_inst_70_);
v___x_83_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, lean_box(0));
lean_closure_set(v___x_83_, 2, v_inst_70_);
lean_closure_set(v___x_83_, 3, v___f_82_);
v___x_84_ = l_Array_repr___redArg(v___x_83_, v_entries_73_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 4);
lean_ctor_set(v___x_76_, 1, v___x_84_);
lean_ctor_set(v___x_76_, 0, v___x_81_);
v___x_86_ = v___x_76_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_81_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_84_);
v___x_86_ = v_reuseFailAlloc_124_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_80_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__12));
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_box(1);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__14));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_79_);
v___f_97_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__15));
v___x_98_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, lean_box(0));
lean_closure_set(v___x_98_, 2, v_inst_70_);
lean_closure_set(v___x_98_, 3, v___f_97_);
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__17));
v___x_101_ = lean_box(0);
v___x_102_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_103_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_102_, v___f_78_, v_indexes_74_, v___x_101_, v___x_99_);
lean_dec_ref(v_indexes_74_);
v___x_104_ = l_List_repr___redArg(v___x_98_, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_100_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = l_Repr_addAppParen(v___x_105_, v___x_99_);
v___x_107_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_81_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_87_);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_96_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_90_);
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_92_);
v___x_112_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__29));
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_79_);
v___x_115_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__31));
v___x_116_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_obj_once(&l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34, &l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34_once, _init_l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__34);
v___x_118_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__35));
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_116_);
v___x_120_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__36));
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_117_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_87_);
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_x_132_, lean_object* v_prec_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Std_Internal_instReprIndexMultiMap_repr___redArg(v_inst_130_, v_inst_131_, v_x_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap_repr___boxed(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_x_141_, lean_object* v_prec_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_Internal_instReprIndexMultiMap_repr(v_00_u03b1_135_, v_00_u03b2_136_, v_inst_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_x_141_, v_prec_142_);
lean_dec(v_prec_142_);
lean_dec_ref(v_inst_138_);
lean_dec_ref(v_inst_137_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap___redArg(lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_148_, 0, lean_box(0));
lean_closure_set(v___x_148_, 1, lean_box(0));
lean_closure_set(v___x_148_, 2, v_inst_144_);
lean_closure_set(v___x_148_, 3, v_inst_145_);
lean_closure_set(v___x_148_, 4, v_inst_146_);
lean_closure_set(v___x_148_, 5, v_inst_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instReprIndexMultiMap(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_closure((void*)(l_Std_Internal_instReprIndexMultiMap_repr___boxed), 8, 6);
lean_closure_set(v___x_155_, 0, lean_box(0));
lean_closure_set(v___x_155_, 1, lean_box(0));
lean_closure_set(v___x_155_, 2, v_inst_151_);
lean_closure_set(v___x_155_, 3, v_inst_152_);
lean_closure_set(v___x_155_, 4, v_inst_153_);
lean_closure_set(v___x_155_, 5, v_inst_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1(void){
_start:
{
lean_object* v_cellCount_158_; lean_object* v___x_159_; 
v_cellCount_158_ = lean_unsigned_to_nat(16u);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2(void){
_start:
{
lean_object* v_cellCount_160_; lean_object* v___x_161_; 
v_cellCount_160_ = lean_unsigned_to_nat(16u);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__2, &l_Std_Internal_instInhabitedIndexMultiMap___closed__2_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__2);
v___x_163_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__1, &l_Std_Internal_instInhabitedIndexMultiMap___closed__1_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__1);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_162_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__4(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__3, &l_Std_Internal_instInhabitedIndexMultiMap___closed__3_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__3);
v___x_167_ = ((lean_object*)(l_Std_Internal_instInhabitedIndexMultiMap___closed__0));
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__4, &l_Std_Internal_instInhabitedIndexMultiMap___closed__4_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__4);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_instInhabitedIndexMultiMap___boxed(lean_object* v_00_u03b1_176_, lean_object* v_00_u03b2_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Internal_instInhabitedIndexMultiMap(v_00_u03b1_176_, v_00_u03b2_177_, v_inst_178_, v_inst_179_, v_inst_180_, v_inst_181_);
lean_dec(v_inst_181_);
lean_dec(v_inst_180_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_inst_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instMembership___boxed(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Internal_IndexMultiMap_instMembership(v_00_u03b1_188_, v_00_u03b2_189_, v_inst_190_, v_inst_191_);
lean_dec_ref(v_inst_191_);
lean_dec_ref(v_inst_190_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_key_195_, lean_object* v_map_196_){
_start:
{
lean_object* v_indexes_197_; uint8_t v___x_198_; 
v_indexes_197_ = lean_ctor_get(v_map_196_, 1);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_193_, v_inst_194_, v_indexes_197_, v_key_195_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___redArg___boxed(lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_key_201_, lean_object* v_map_202_){
_start:
{
uint8_t v_res_203_; lean_object* v_r_204_; 
v_res_203_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_199_, v_inst_200_, v_key_201_, v_map_202_);
lean_dec_ref(v_map_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_instDecidableMem(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_key_209_, lean_object* v_map_210_){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_207_, v_inst_208_, v_key_209_, v_map_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instDecidableMem___boxed(lean_object* v_00_u03b1_212_, lean_object* v_00_u03b2_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_key_216_, lean_object* v_map_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_Internal_IndexMultiMap_instDecidableMem(v_00_u03b1_212_, v_00_u03b2_213_, v_inst_214_, v_inst_215_, v_key_216_, v_map_217_);
lean_dec_ref(v_map_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(lean_object* v_val_220_, lean_object* v_entries_221_, lean_object* v_x1_222_, lean_object* v_x2_223_, lean_object* v_x3_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_snd_227_; 
v___x_225_ = lean_array_fget_borrowed(v_val_220_, v_x1_222_);
v___x_226_ = lean_array_fget_borrowed(v_entries_221_, v___x_225_);
v_snd_227_ = lean_ctor_get(v___x_226_, 1);
lean_inc(v_snd_227_);
return v_snd_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed(lean_object* v_val_228_, lean_object* v_entries_229_, lean_object* v_x1_230_, lean_object* v_x2_231_, lean_object* v_x3_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0(v_val_228_, v_entries_229_, v_x1_230_, v_x2_231_, v_x3_232_);
lean_dec(v_x2_231_);
lean_dec(v_x1_230_);
lean_dec_ref(v_entries_229_);
lean_dec_ref(v_val_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll___redArg(lean_object* v_inst_234_, lean_object* v_inst_235_, lean_object* v_map_236_, lean_object* v_key_237_){
_start:
{
lean_object* v_entries_238_; lean_object* v_indexes_239_; lean_object* v___x_240_; lean_object* v_val_241_; lean_object* v___f_242_; lean_object* v___x_243_; size_t v_sz_244_; size_t v___x_245_; lean_object* v_entries_246_; 
v_entries_238_ = lean_ctor_get(v_map_236_, 0);
lean_inc_ref(v_entries_238_);
v_indexes_239_ = lean_ctor_get(v_map_236_, 1);
lean_inc_ref(v_indexes_239_);
lean_dec_ref(v_map_236_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_234_, v_inst_235_, v_indexes_239_, v_key_237_);
lean_dec_ref(v_indexes_239_);
v_val_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc_n(v_val_241_, 3);
lean_dec(v___x_240_);
v___f_242_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_242_, 0, v_val_241_);
lean_closure_set(v___f_242_, 1, v_entries_238_);
v___x_243_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_244_ = lean_array_size(v_val_241_);
v___x_245_ = ((size_t)0ULL);
v_entries_246_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_243_, v_val_241_, v___f_242_, v_sz_244_, v___x_245_, v_val_241_);
lean_dec(v_val_241_);
return v_entries_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_map_251_, lean_object* v_key_252_, lean_object* v_h_253_){
_start:
{
lean_object* v_entries_254_; lean_object* v_indexes_255_; lean_object* v___x_256_; lean_object* v_val_257_; lean_object* v___f_258_; lean_object* v___x_259_; size_t v_sz_260_; size_t v___x_261_; lean_object* v_entries_262_; 
v_entries_254_ = lean_ctor_get(v_map_251_, 0);
lean_inc_ref(v_entries_254_);
v_indexes_255_ = lean_ctor_get(v_map_251_, 1);
lean_inc_ref(v_indexes_255_);
lean_dec_ref(v_map_251_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_249_, v_inst_250_, v_indexes_255_, v_key_252_);
lean_dec_ref(v_indexes_255_);
v_val_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc_n(v_val_257_, 3);
lean_dec(v___x_256_);
v___f_258_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_258_, 0, v_val_257_);
lean_closure_set(v___f_258_, 1, v_entries_254_);
v___x_259_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_260_ = lean_array_size(v_val_257_);
v___x_261_ = ((size_t)0ULL);
v_entries_262_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_259_, v_val_257_, v___f_258_, v_sz_260_, v___x_261_, v_val_257_);
lean_dec(v_val_257_);
return v_entries_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg(lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_map_265_, lean_object* v_key_266_){
_start:
{
lean_object* v_entries_267_; lean_object* v_indexes_268_; lean_object* v___x_269_; lean_object* v_val_270_; lean_object* v___x_271_; lean_object* v_entry_272_; lean_object* v___x_273_; lean_object* v_snd_274_; 
v_entries_267_ = lean_ctor_get(v_map_265_, 0);
v_indexes_268_ = lean_ctor_get(v_map_265_, 1);
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_263_, v_inst_264_, v_indexes_268_, v_key_266_);
v_val_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_val_270_);
lean_dec(v___x_269_);
v___x_271_ = lean_unsigned_to_nat(0u);
v_entry_272_ = lean_array_fget(v_val_270_, v___x_271_);
lean_dec(v_val_270_);
v___x_273_ = lean_array_fget_borrowed(v_entries_267_, v_entry_272_);
lean_dec(v_entry_272_);
v_snd_274_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_snd_274_);
return v_snd_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___redArg___boxed(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_map_277_, lean_object* v_key_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Internal_IndexMultiMap_get___redArg(v_inst_275_, v_inst_276_, v_map_277_, v_key_278_);
lean_dec_ref(v_map_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_map_284_, lean_object* v_key_285_, lean_object* v_h_286_){
_start:
{
lean_object* v_entries_287_; lean_object* v_indexes_288_; lean_object* v___x_289_; lean_object* v_val_290_; lean_object* v___x_291_; lean_object* v_entry_292_; lean_object* v___x_293_; lean_object* v_snd_294_; 
v_entries_287_ = lean_ctor_get(v_map_284_, 0);
v_indexes_288_ = lean_ctor_get(v_map_284_, 1);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_282_, v_inst_283_, v_indexes_288_, v_key_285_);
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec(v___x_289_);
v___x_291_ = lean_unsigned_to_nat(0u);
v_entry_292_ = lean_array_fget(v_val_290_, v___x_291_);
lean_dec(v_val_290_);
v___x_293_ = lean_array_fget_borrowed(v_entries_287_, v_entry_292_);
lean_dec(v_entry_292_);
v_snd_294_ = lean_ctor_get(v___x_293_, 1);
lean_inc(v_snd_294_);
return v_snd_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get___boxed(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_map_299_, lean_object* v_key_300_, lean_object* v_h_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Internal_IndexMultiMap_get(v_00_u03b1_295_, v_00_u03b2_296_, v_inst_297_, v_inst_298_, v_map_299_, v_key_300_, v_h_301_);
lean_dec_ref(v_map_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f___redArg(lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_map_305_, lean_object* v_key_306_){
_start:
{
uint8_t v___x_307_; 
lean_inc(v_key_306_);
lean_inc_ref(v_inst_304_);
lean_inc_ref(v_inst_303_);
v___x_307_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_303_, v_inst_304_, v_key_306_, v_map_305_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_dec(v_key_306_);
lean_dec_ref(v_map_305_);
lean_dec_ref(v_inst_304_);
lean_dec_ref(v_inst_303_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v_entries_309_; lean_object* v_indexes_310_; lean_object* v___x_311_; lean_object* v_val_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_324_; 
v_entries_309_ = lean_ctor_get(v_map_305_, 0);
lean_inc_ref(v_entries_309_);
v_indexes_310_ = lean_ctor_get(v_map_305_, 1);
lean_inc_ref(v_indexes_310_);
lean_dec_ref(v_map_305_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_303_, v_inst_304_, v_indexes_310_, v_key_306_);
lean_dec_ref(v_indexes_310_);
v_val_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_324_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_val_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___f_316_; lean_object* v___x_317_; size_t v_sz_318_; size_t v___x_319_; lean_object* v_entries_320_; lean_object* v___x_322_; 
lean_inc_n(v_val_312_, 2);
v___f_316_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_316_, 0, v_val_312_);
lean_closure_set(v___f_316_, 1, v_entries_309_);
v___x_317_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_318_ = lean_array_size(v_val_312_);
v___x_319_ = ((size_t)0ULL);
v_entries_320_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_317_, v_val_312_, v___f_316_, v_sz_318_, v___x_319_, v_val_312_);
lean_dec(v_val_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_entries_320_);
v___x_322_ = v___x_314_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_entries_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getAll_x3f(lean_object* v_00_u03b1_325_, lean_object* v_00_u03b2_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_map_329_, lean_object* v_key_330_){
_start:
{
uint8_t v___x_331_; 
lean_inc(v_key_330_);
lean_inc_ref(v_inst_328_);
lean_inc_ref(v_inst_327_);
v___x_331_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_327_, v_inst_328_, v_key_330_, v_map_329_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
lean_dec(v_key_330_);
lean_dec_ref(v_map_329_);
lean_dec_ref(v_inst_328_);
lean_dec_ref(v_inst_327_);
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v_entries_333_; lean_object* v_indexes_334_; lean_object* v___x_335_; lean_object* v_val_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_348_; 
v_entries_333_ = lean_ctor_get(v_map_329_, 0);
lean_inc_ref(v_entries_333_);
v_indexes_334_ = lean_ctor_get(v_map_329_, 1);
lean_inc_ref(v_indexes_334_);
lean_dec_ref(v_map_329_);
v___x_335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_327_, v_inst_328_, v_indexes_334_, v_key_330_);
lean_dec_ref(v_indexes_334_);
v_val_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_348_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_val_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_348_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___f_340_; lean_object* v___x_341_; size_t v_sz_342_; size_t v___x_343_; lean_object* v_entries_344_; lean_object* v___x_346_; 
lean_inc_n(v_val_336_, 2);
v___f_340_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_340_, 0, v_val_336_);
lean_closure_set(v___f_340_, 1, v_entries_333_);
v___x_341_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_342_ = lean_array_size(v_val_336_);
v___x_343_ = ((size_t)0ULL);
v_entries_344_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_341_, v_val_336_, v___f_340_, v_sz_342_, v___x_343_, v_val_336_);
lean_dec(v_val_336_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v_entries_344_);
v___x_346_ = v___x_338_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_entries_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg(lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_map_351_, lean_object* v_key_352_){
_start:
{
uint8_t v___x_353_; 
lean_inc(v_key_352_);
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
v___x_353_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_349_, v_inst_350_, v_key_352_, v_map_351_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v_key_352_);
lean_dec_ref(v_inst_350_);
lean_dec_ref(v_inst_349_);
v___x_354_ = lean_box(0);
return v___x_354_;
}
else
{
lean_object* v_entries_355_; lean_object* v_indexes_356_; lean_object* v___x_357_; lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_369_; 
v_entries_355_ = lean_ctor_get(v_map_351_, 0);
v_indexes_356_ = lean_ctor_get(v_map_351_, 1);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_349_, v_inst_350_, v_indexes_356_, v_key_352_);
v_val_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_369_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_369_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v_entry_363_; lean_object* v___x_364_; lean_object* v_snd_365_; lean_object* v___x_367_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v_entry_363_ = lean_array_fget(v_val_358_, v___x_362_);
lean_dec(v_val_358_);
v___x_364_ = lean_array_fget_borrowed(v_entries_355_, v_entry_363_);
lean_dec(v_entry_363_);
v_snd_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_snd_365_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_snd_365_);
v___x_367_ = v___x_360_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_snd_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___redArg___boxed(lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_map_372_, lean_object* v_key_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Internal_IndexMultiMap_get_x3f___redArg(v_inst_370_, v_inst_371_, v_map_372_, v_key_373_);
lean_dec_ref(v_map_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_map_379_, lean_object* v_key_380_){
_start:
{
uint8_t v___x_381_; 
lean_inc(v_key_380_);
lean_inc_ref(v_inst_378_);
lean_inc_ref(v_inst_377_);
v___x_381_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_377_, v_inst_378_, v_key_380_, v_map_379_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_key_380_);
lean_dec_ref(v_inst_378_);
lean_dec_ref(v_inst_377_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v_entries_383_; lean_object* v_indexes_384_; lean_object* v___x_385_; lean_object* v_val_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_397_; 
v_entries_383_ = lean_ctor_get(v_map_379_, 0);
v_indexes_384_ = lean_ctor_get(v_map_379_, 1);
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_377_, v_inst_378_, v_indexes_384_, v_key_380_);
v_val_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_val_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_397_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v_entry_391_; lean_object* v___x_392_; lean_object* v_snd_393_; lean_object* v___x_395_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v_entry_391_ = lean_array_fget(v_val_386_, v___x_390_);
lean_dec(v_val_386_);
v___x_392_ = lean_array_fget_borrowed(v_entries_383_, v_entry_391_);
lean_dec(v_entry_391_);
v_snd_393_ = lean_ctor_get(v___x_392_, 1);
lean_inc(v_snd_393_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v_snd_393_);
v___x_395_ = v___x_388_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_snd_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x3f___boxed(lean_object* v_00_u03b1_398_, lean_object* v_00_u03b2_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_map_402_, lean_object* v_key_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_Internal_IndexMultiMap_get_x3f(v_00_u03b1_398_, v_00_u03b2_399_, v_inst_400_, v_inst_401_, v_map_402_, v_key_403_);
lean_dec_ref(v_map_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(lean_object* v_inst_405_, lean_object* v_value_406_, lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v_a_409_, lean_object* v_x_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
lean_inc(v_a_409_);
v___x_412_ = lean_apply_2(v_inst_405_, v_a_409_, v_value_406_);
v___x_413_ = lean_unbox(v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v_a_409_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_407_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v___x_407_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_a_409_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_408_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed(lean_object* v_inst_419_, lean_object* v_value_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v_a_423_, lean_object* v_x_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1(v_inst_419_, v_value_420_, v___x_421_, v___x_422_, v_a_423_, v_x_424_, v___y_425_);
lean_dec_ref(v___y_425_);
return v_res_426_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry___redArg(lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_map_432_, lean_object* v_inst_433_, lean_object* v_key_434_, lean_object* v_value_435_){
_start:
{
uint8_t v___x_436_; 
lean_inc(v_key_434_);
lean_inc_ref(v_inst_431_);
lean_inc_ref(v_inst_430_);
v___x_436_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_430_, v_inst_431_, v_key_434_, v_map_432_);
if (v___x_436_ == 0)
{
lean_dec(v_value_435_);
lean_dec(v_key_434_);
lean_dec_ref(v_inst_433_);
lean_dec_ref(v_map_432_);
lean_dec_ref(v_inst_431_);
lean_dec_ref(v_inst_430_);
return v___x_436_;
}
else
{
lean_object* v_entries_437_; lean_object* v_indexes_438_; lean_object* v___x_439_; lean_object* v_val_440_; lean_object* v___f_441_; lean_object* v___x_442_; size_t v_sz_443_; size_t v___x_444_; lean_object* v_entries_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___f_448_; size_t v_sz_449_; lean_object* v___x_450_; lean_object* v_fst_451_; 
v_entries_437_ = lean_ctor_get(v_map_432_, 0);
lean_inc_ref(v_entries_437_);
v_indexes_438_ = lean_ctor_get(v_map_432_, 1);
lean_inc_ref(v_indexes_438_);
lean_dec_ref(v_map_432_);
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_430_, v_inst_431_, v_indexes_438_, v_key_434_);
lean_dec_ref(v_indexes_438_);
v_val_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc_n(v_val_440_, 3);
lean_dec(v___x_439_);
v___f_441_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_441_, 0, v_val_440_);
lean_closure_set(v___f_441_, 1, v_entries_437_);
v___x_442_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_443_ = lean_array_size(v_val_440_);
v___x_444_ = ((size_t)0ULL);
v_entries_445_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_442_, v_val_440_, v___f_441_, v_sz_443_, v___x_444_, v_val_440_);
lean_dec(v_val_440_);
v___x_446_ = lean_box(0);
v___x_447_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_448_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_448_, 0, v_inst_433_);
lean_closure_set(v___f_448_, 1, v_value_435_);
lean_closure_set(v___f_448_, 2, v___x_447_);
lean_closure_set(v___f_448_, 3, v___x_446_);
v_sz_449_ = lean_array_size(v_entries_445_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_442_, v_entries_445_, v___f_448_, v_sz_449_, v___x_444_, v___x_447_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_fst_451_);
lean_dec(v___x_450_);
if (lean_obj_tag(v_fst_451_) == 0)
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
else
{
lean_object* v_val_453_; 
v_val_453_ = lean_ctor_get(v_fst_451_, 0);
lean_inc(v_val_453_);
lean_dec_ref_known(v_fst_451_, 1);
if (lean_obj_tag(v_val_453_) == 0)
{
uint8_t v___x_454_; 
v___x_454_ = 0;
return v___x_454_;
}
else
{
lean_dec_ref_known(v_val_453_, 1);
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___redArg___boxed(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_map_457_, lean_object* v_inst_458_, lean_object* v_key_459_, lean_object* v_value_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Std_Internal_IndexMultiMap_hasEntry___redArg(v_inst_455_, v_inst_456_, v_map_457_, v_inst_458_, v_key_459_, v_value_460_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_hasEntry(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_map_467_, lean_object* v_inst_468_, lean_object* v_key_469_, lean_object* v_value_470_){
_start:
{
uint8_t v___x_471_; 
lean_inc(v_key_469_);
lean_inc_ref(v_inst_466_);
lean_inc_ref(v_inst_465_);
v___x_471_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_465_, v_inst_466_, v_key_469_, v_map_467_);
if (v___x_471_ == 0)
{
lean_dec(v_value_470_);
lean_dec(v_key_469_);
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_map_467_);
lean_dec_ref(v_inst_466_);
lean_dec_ref(v_inst_465_);
return v___x_471_;
}
else
{
lean_object* v_entries_472_; lean_object* v_indexes_473_; lean_object* v___x_474_; lean_object* v_val_475_; lean_object* v___f_476_; lean_object* v___x_477_; size_t v_sz_478_; size_t v___x_479_; lean_object* v_entries_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___f_483_; size_t v_sz_484_; lean_object* v___x_485_; lean_object* v_fst_486_; 
v_entries_472_ = lean_ctor_get(v_map_467_, 0);
lean_inc_ref(v_entries_472_);
v_indexes_473_ = lean_ctor_get(v_map_467_, 1);
lean_inc_ref(v_indexes_473_);
lean_dec_ref(v_map_467_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_465_, v_inst_466_, v_indexes_473_, v_key_469_);
lean_dec_ref(v_indexes_473_);
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_n(v_val_475_, 3);
lean_dec(v___x_474_);
v___f_476_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_476_, 0, v_val_475_);
lean_closure_set(v___f_476_, 1, v_entries_472_);
v___x_477_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_478_ = lean_array_size(v_val_475_);
v___x_479_ = ((size_t)0ULL);
v_entries_480_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_477_, v_val_475_, v___f_476_, v_sz_478_, v___x_479_, v_val_475_);
lean_dec(v_val_475_);
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___closed__0));
v___f_483_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_hasEntry___redArg___lam__1___boxed), 7, 4);
lean_closure_set(v___f_483_, 0, v_inst_468_);
lean_closure_set(v___f_483_, 1, v_value_470_);
lean_closure_set(v___f_483_, 2, v___x_482_);
lean_closure_set(v___f_483_, 3, v___x_481_);
v_sz_484_ = lean_array_size(v_entries_480_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_477_, v_entries_480_, v___f_483_, v_sz_484_, v___x_479_, v___x_482_);
v_fst_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_fst_486_);
lean_dec(v___x_485_);
if (lean_obj_tag(v_fst_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 0;
return v___x_487_;
}
else
{
lean_object* v_val_488_; 
v_val_488_ = lean_ctor_get(v_fst_486_, 0);
lean_inc(v_val_488_);
lean_dec_ref_known(v_fst_486_, 1);
if (lean_obj_tag(v_val_488_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
else
{
lean_dec_ref_known(v_val_488_, 1);
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_hasEntry___boxed(lean_object* v_00_u03b1_490_, lean_object* v_00_u03b2_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_map_494_, lean_object* v_inst_495_, lean_object* v_key_496_, lean_object* v_value_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_Internal_IndexMultiMap_hasEntry(v_00_u03b1_490_, v_00_u03b2_491_, v_inst_492_, v_inst_493_, v_map_494_, v_inst_495_, v_key_496_, v_value_497_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f___redArg(lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_map_502_, lean_object* v_key_503_){
_start:
{
uint8_t v___x_504_; 
lean_inc(v_key_503_);
lean_inc_ref(v_inst_501_);
lean_inc_ref(v_inst_500_);
v___x_504_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_500_, v_inst_501_, v_key_503_, v_map_502_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v_key_503_);
lean_dec_ref(v_map_502_);
lean_dec_ref(v_inst_501_);
lean_dec_ref(v_inst_500_);
v___x_505_ = lean_box(0);
return v___x_505_;
}
else
{
lean_object* v_entries_506_; lean_object* v_indexes_507_; lean_object* v___x_508_; lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_527_; 
v_entries_506_ = lean_ctor_get(v_map_502_, 0);
lean_inc_ref(v_entries_506_);
v_indexes_507_ = lean_ctor_get(v_map_502_, 1);
lean_inc_ref(v_indexes_507_);
lean_dec_ref(v_map_502_);
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_500_, v_inst_501_, v_indexes_507_, v_key_503_);
lean_dec_ref(v_indexes_507_);
v_val_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_527_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___f_513_; lean_object* v___x_514_; size_t v_sz_515_; size_t v___x_516_; lean_object* v_entries_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
lean_inc_n(v_val_509_, 2);
v___f_513_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_513_, 0, v_val_509_);
lean_closure_set(v___f_513_, 1, v_entries_506_);
v___x_514_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_515_ = lean_array_size(v_val_509_);
v___x_516_ = ((size_t)0ULL);
v_entries_517_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_514_, v_val_509_, v___f_513_, v_sz_515_, v___x_516_, v_val_509_);
lean_dec(v_val_509_);
v___x_518_ = lean_array_get_size(v_entries_517_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_sub(v___x_518_, v___x_519_);
v___x_521_ = lean_nat_dec_lt(v___x_520_, v___x_518_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v___x_520_);
lean_dec(v_entries_517_);
lean_del_object(v___x_511_);
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_array_fget(v_entries_517_, v___x_520_);
lean_dec(v___x_520_);
lean_dec(v_entries_517_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_523_);
v___x_525_ = v___x_511_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getLast_x3f(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_map_532_, lean_object* v_key_533_){
_start:
{
uint8_t v___x_534_; 
lean_inc(v_key_533_);
lean_inc_ref(v_inst_531_);
lean_inc_ref(v_inst_530_);
v___x_534_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_530_, v_inst_531_, v_key_533_, v_map_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v_key_533_);
lean_dec_ref(v_map_532_);
lean_dec_ref(v_inst_531_);
lean_dec_ref(v_inst_530_);
v___x_535_ = lean_box(0);
return v___x_535_;
}
else
{
lean_object* v_entries_536_; lean_object* v_indexes_537_; lean_object* v___x_538_; lean_object* v_val_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_557_; 
v_entries_536_ = lean_ctor_get(v_map_532_, 0);
lean_inc_ref(v_entries_536_);
v_indexes_537_ = lean_ctor_get(v_map_532_, 1);
lean_inc_ref(v_indexes_537_);
lean_dec_ref(v_map_532_);
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_530_, v_inst_531_, v_indexes_537_, v_key_533_);
lean_dec_ref(v_indexes_537_);
v_val_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_557_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_557_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_val_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_557_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___f_543_; lean_object* v___x_544_; size_t v_sz_545_; size_t v___x_546_; lean_object* v_entries_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
lean_inc_n(v_val_539_, 2);
v___f_543_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_getAll___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_543_, 0, v_val_539_);
lean_closure_set(v___f_543_, 1, v_entries_536_);
v___x_544_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v_sz_545_ = lean_array_size(v_val_539_);
v___x_546_ = ((size_t)0ULL);
v_entries_547_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_544_, v_val_539_, v___f_543_, v_sz_545_, v___x_546_, v_val_539_);
lean_dec(v_val_539_);
v___x_548_ = lean_array_get_size(v_entries_547_);
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_sub(v___x_548_, v___x_549_);
v___x_551_ = lean_nat_dec_lt(v___x_550_, v___x_548_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec(v___x_550_);
lean_dec(v_entries_547_);
lean_del_object(v___x_541_);
v___x_552_ = lean_box(0);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_array_fget(v_entries_547_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v_entries_547_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_553_);
v___x_555_ = v___x_541_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg(lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_map_560_, lean_object* v_key_561_, lean_object* v_d_562_){
_start:
{
uint8_t v___x_563_; 
lean_inc(v_key_561_);
lean_inc_ref(v_inst_559_);
lean_inc_ref(v_inst_558_);
v___x_563_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_558_, v_inst_559_, v_key_561_, v_map_560_);
if (v___x_563_ == 0)
{
lean_dec(v_key_561_);
lean_dec_ref(v_inst_559_);
lean_dec_ref(v_inst_558_);
lean_inc(v_d_562_);
return v_d_562_;
}
else
{
lean_object* v_entries_564_; lean_object* v_indexes_565_; lean_object* v___x_566_; lean_object* v_val_567_; lean_object* v___x_568_; lean_object* v_entry_569_; lean_object* v___x_570_; lean_object* v_snd_571_; 
v_entries_564_ = lean_ctor_get(v_map_560_, 0);
v_indexes_565_ = lean_ctor_get(v_map_560_, 1);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_558_, v_inst_559_, v_indexes_565_, v_key_561_);
v_val_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_val_567_);
lean_dec(v___x_566_);
v___x_568_ = lean_unsigned_to_nat(0u);
v_entry_569_ = lean_array_fget(v_val_567_, v___x_568_);
lean_dec(v_val_567_);
v___x_570_ = lean_array_fget_borrowed(v_entries_564_, v_entry_569_);
lean_dec(v_entry_569_);
v_snd_571_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_571_);
return v_snd_571_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___redArg___boxed(lean_object* v_inst_572_, lean_object* v_inst_573_, lean_object* v_map_574_, lean_object* v_key_575_, lean_object* v_d_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Internal_IndexMultiMap_getD___redArg(v_inst_572_, v_inst_573_, v_map_574_, v_key_575_, v_d_576_);
lean_dec(v_d_576_);
lean_dec_ref(v_map_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_map_582_, lean_object* v_key_583_, lean_object* v_d_584_){
_start:
{
uint8_t v___x_585_; 
lean_inc(v_key_583_);
lean_inc_ref(v_inst_581_);
lean_inc_ref(v_inst_580_);
v___x_585_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_580_, v_inst_581_, v_key_583_, v_map_582_);
if (v___x_585_ == 0)
{
lean_dec(v_key_583_);
lean_dec_ref(v_inst_581_);
lean_dec_ref(v_inst_580_);
lean_inc(v_d_584_);
return v_d_584_;
}
else
{
lean_object* v_entries_586_; lean_object* v_indexes_587_; lean_object* v___x_588_; lean_object* v_val_589_; lean_object* v___x_590_; lean_object* v_entry_591_; lean_object* v___x_592_; lean_object* v_snd_593_; 
v_entries_586_ = lean_ctor_get(v_map_582_, 0);
v_indexes_587_ = lean_ctor_get(v_map_582_, 1);
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_580_, v_inst_581_, v_indexes_587_, v_key_583_);
v_val_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_val_589_);
lean_dec(v___x_588_);
v___x_590_ = lean_unsigned_to_nat(0u);
v_entry_591_ = lean_array_fget(v_val_589_, v___x_590_);
lean_dec(v_val_589_);
v___x_592_ = lean_array_fget_borrowed(v_entries_586_, v_entry_591_);
lean_dec(v_entry_591_);
v_snd_593_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_snd_593_);
return v_snd_593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_getD___boxed(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_inst_596_, lean_object* v_inst_597_, lean_object* v_map_598_, lean_object* v_key_599_, lean_object* v_d_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Internal_IndexMultiMap_getD(v_00_u03b1_594_, v_00_u03b2_595_, v_inst_596_, v_inst_597_, v_map_598_, v_key_599_, v_d_600_);
lean_dec(v_d_600_);
lean_dec_ref(v_map_598_);
return v_res_601_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_605_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__2));
v___x_606_ = lean_unsigned_to_nat(14u);
v___x_607_ = lean_unsigned_to_nat(22u);
v___x_608_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__1));
v___x_609_ = ((lean_object*)(l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__0));
v___x_610_ = l_mkPanicMessageWithDecl(v___x_609_, v___x_608_, v___x_607_, v___x_606_, v___x_605_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg(lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_map_614_, lean_object* v_key_615_){
_start:
{
uint8_t v___x_616_; 
lean_inc(v_key_615_);
lean_inc_ref(v_inst_612_);
lean_inc_ref(v_inst_611_);
v___x_616_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_611_, v_inst_612_, v_key_615_, v_map_614_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v_key_615_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_inst_611_);
v___x_617_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_618_ = l_panic___redArg(v_inst_613_, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v_entries_619_; lean_object* v_indexes_620_; lean_object* v___x_621_; lean_object* v_val_622_; lean_object* v___x_623_; lean_object* v_entry_624_; lean_object* v___x_625_; lean_object* v_snd_626_; 
v_entries_619_ = lean_ctor_get(v_map_614_, 0);
v_indexes_620_ = lean_ctor_get(v_map_614_, 1);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_611_, v_inst_612_, v_indexes_620_, v_key_615_);
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec(v___x_621_);
v___x_623_ = lean_unsigned_to_nat(0u);
v_entry_624_ = lean_array_fget(v_val_622_, v___x_623_);
lean_dec(v_val_622_);
v___x_625_ = lean_array_fget_borrowed(v_entries_619_, v_entry_624_);
lean_dec(v_entry_624_);
v_snd_626_ = lean_ctor_get(v___x_625_, 1);
lean_inc(v_snd_626_);
return v_snd_626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___redArg___boxed(lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_map_630_, lean_object* v_key_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Std_Internal_IndexMultiMap_get_x21___redArg(v_inst_627_, v_inst_628_, v_inst_629_, v_map_630_, v_key_631_);
lean_dec_ref(v_map_630_);
lean_dec(v_inst_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_inst_635_, lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_map_638_, lean_object* v_key_639_){
_start:
{
uint8_t v___x_640_; 
lean_inc(v_key_639_);
lean_inc_ref(v_inst_636_);
lean_inc_ref(v_inst_635_);
v___x_640_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_635_, v_inst_636_, v_key_639_, v_map_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_key_639_);
lean_dec_ref(v_inst_636_);
lean_dec_ref(v_inst_635_);
v___x_641_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3, &l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3_once, _init_l_Std_Internal_IndexMultiMap_get_x21___redArg___closed__3);
v___x_642_ = l_panic___redArg(v_inst_637_, v___x_641_);
return v___x_642_;
}
else
{
lean_object* v_entries_643_; lean_object* v_indexes_644_; lean_object* v___x_645_; lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v_entry_648_; lean_object* v___x_649_; lean_object* v_snd_650_; 
v_entries_643_ = lean_ctor_get(v_map_638_, 0);
v_indexes_644_ = lean_ctor_get(v_map_638_, 1);
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_635_, v_inst_636_, v_indexes_644_, v_key_639_);
v_val_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_val_646_);
lean_dec(v___x_645_);
v___x_647_ = lean_unsigned_to_nat(0u);
v_entry_648_ = lean_array_fget(v_val_646_, v___x_647_);
lean_dec(v_val_646_);
v___x_649_ = lean_array_fget_borrowed(v_entries_643_, v_entry_648_);
lean_dec(v_entry_648_);
v_snd_650_ = lean_ctor_get(v___x_649_, 1);
lean_inc(v_snd_650_);
return v_snd_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_get_x21___boxed(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_map_656_, lean_object* v_key_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_Internal_IndexMultiMap_get_x21(v_00_u03b1_651_, v_00_u03b2_652_, v_inst_653_, v_inst_654_, v_inst_655_, v_map_656_, v_key_657_);
lean_dec_ref(v_map_656_);
lean_dec(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter___redArg(lean_object* v_x_659_, lean_object* v_h__1_660_, lean_object* v_h__2_661_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_h__1_660_);
v___x_662_ = lean_box(0);
v___x_663_ = lean_apply_1(v_h__2_661_, v___x_662_);
return v___x_663_;
}
else
{
lean_object* v_val_664_; lean_object* v___x_665_; 
lean_dec(v_h__2_661_);
v_val_664_ = lean_ctor_get(v_x_659_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_x_659_, 1);
v___x_665_ = lean_apply_1(v_h__1_660_, v_val_664_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Internal_IndexMultiMap_0__Std_Internal_IndexMultiMap_insert_match__1_splitter(lean_object* v_motive_666_, lean_object* v_x_667_, lean_object* v_h__1_668_, lean_object* v_h__2_669_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_h__1_668_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_apply_1(v_h__2_669_, v___x_670_);
return v___x_671_;
}
else
{
lean_object* v_val_672_; lean_object* v___x_673_; 
lean_dec(v_h__2_669_);
v_val_672_ = lean_ctor_get(v_x_667_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_x_667_, 1);
v___x_673_ = lean_apply_1(v_h__1_668_, v_val_672_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(lean_object* v_i_674_, lean_object* v_x_675_){
_start:
{
if (lean_obj_tag(v_x_675_) == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_mk_empty_array_with_capacity(v___x_676_);
v___x_678_ = lean_array_push(v___x_677_, v_i_674_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
else
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_688_; 
v_val_680_ = lean_ctor_get(v_x_675_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_675_);
if (v_isSharedCheck_688_ == 0)
{
v___x_682_ = v_x_675_;
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_x_675_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_688_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = lean_array_push(v_val_680_, v_i_674_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_684_);
v___x_686_ = v___x_682_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert___redArg(lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_map_691_, lean_object* v_key_692_, lean_object* v_value_693_){
_start:
{
lean_object* v_entries_694_; lean_object* v_indexes_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_790_; 
v_entries_694_ = lean_ctor_get(v_map_691_, 0);
v_indexes_695_ = lean_ctor_get(v_map_691_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_map_691_);
if (v_isSharedCheck_790_ == 0)
{
v___x_697_ = v_map_691_;
v_isShared_698_ = v_isSharedCheck_790_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_indexes_695_);
lean_inc(v_entries_694_);
lean_dec(v_map_691_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_790_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_i_699_; lean_object* v___x_700_; lean_object* v_entries_701_; lean_object* v___x_702_; 
v_i_699_ = lean_array_get_size(v_entries_694_);
lean_inc_n(v_key_692_, 2);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_key_692_);
lean_ctor_set(v___x_700_, 1, v_value_693_);
v_entries_701_ = lean_array_push(v_entries_694_, v___x_700_);
lean_inc_ref(v_inst_690_);
lean_inc_ref(v_inst_689_);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_689_, v_inst_690_, v_indexes_695_, v_key_692_);
switch(lean_obj_tag(v___x_702_))
{
case 0:
{
lean_object* v_index_703_; lean_object* v_value_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_val_707_; lean_object* v_size_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec_ref(v_inst_690_);
lean_dec_ref(v_inst_689_);
v_index_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_index_703_);
v_value_704_ = lean_ctor_get(v___x_702_, 2);
lean_inc(v_value_704_);
lean_dec_ref_known(v___x_702_, 3);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v_value_704_);
v___x_706_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_699_, v___x_705_);
v_val_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_val_707_);
lean_dec(v___x_706_);
v_size_708_ = lean_ctor_get(v_indexes_695_, 0);
lean_inc(v_size_708_);
v___x_709_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_695_, v_size_708_, v_index_703_, v_key_692_, v_val_707_);
lean_dec(v_index_703_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_709_);
lean_ctor_set(v___x_697_, 0, v_entries_701_);
v___x_711_ = v___x_697_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_entries_701_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
case 1:
{
lean_object* v_index_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_val_716_; lean_object* v___y_718_; lean_object* v_i_719_; lean_object* v_size_739_; lean_object* v_keyArray_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_index_713_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_index_713_);
lean_dec_ref_known(v___x_702_, 1);
v___x_714_ = lean_box(0);
v___x_715_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_699_, v___x_714_);
v_val_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_val_716_);
lean_dec(v___x_715_);
v_size_739_ = lean_ctor_get(v_indexes_695_, 0);
v_keyArray_740_ = lean_ctor_get(v_indexes_695_, 1);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_add(v_size_739_, v___x_741_);
v___x_743_ = lean_array_get_size(v_keyArray_740_);
v___x_744_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v___x_742_);
lean_dec(v_index_713_);
goto v___jp_727_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_745_ = lean_unsigned_to_nat(4u);
v___x_746_ = lean_nat_mul(v___x_742_, v___x_745_);
v___x_747_ = lean_unsigned_to_nat(3u);
v___x_748_ = lean_nat_mul(v___x_743_, v___x_747_);
v___x_749_ = lean_nat_dec_le(v___x_746_, v___x_748_);
lean_dec(v___x_748_);
lean_dec(v___x_746_);
if (v___x_749_ == 0)
{
lean_dec(v___x_742_);
lean_dec(v_index_713_);
goto v___jp_727_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_del_object(v___x_697_);
lean_dec_ref(v_inst_690_);
lean_dec_ref(v_inst_689_);
v___x_750_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_695_, v___x_742_, v_index_713_, v_key_692_, v_val_716_);
lean_dec(v_index_713_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_entries_701_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
return v___x_751_;
}
}
v___jp_717_:
{
lean_object* v_size_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_size_720_ = lean_ctor_get(v___y_718_, 0);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_size_720_, v___x_721_);
v___x_723_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_718_, v___x_722_, v_i_719_, v_key_692_, v_val_716_);
lean_dec(v_i_719_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_723_);
lean_ctor_set(v___x_697_, 0, v_entries_701_);
v___x_725_ = v___x_697_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_entries_701_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_inc_ref(v_inst_690_);
lean_inc_ref(v_inst_689_);
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_689_, v_inst_690_, v_indexes_695_);
lean_inc(v_key_692_);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_689_, v_inst_690_, v___x_728_, v_key_692_);
switch(lean_obj_tag(v___x_729_))
{
case 0:
{
lean_object* v_index_730_; lean_object* v_size_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_del_object(v___x_697_);
v_index_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_730_);
lean_dec_ref_known(v___x_729_, 3);
v_size_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_size_731_);
v___x_732_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_728_, v_size_731_, v_index_730_, v_key_692_, v_val_716_);
lean_dec(v_index_730_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_entries_701_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
return v___x_733_;
}
case 1:
{
lean_object* v_index_734_; 
v_index_734_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_729_, 1);
v___y_718_ = v___x_728_;
v_i_719_ = v_index_734_;
goto v___jp_717_;
}
default: 
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_728_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_index_737_; 
v_index_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_index_737_);
lean_dec_ref_known(v___x_736_, 1);
v___y_718_ = v___x_728_;
v_i_719_ = v_index_737_;
goto v___jp_717_;
}
else
{
lean_object* v___x_738_; 
lean_dec(v_val_716_);
lean_del_object(v___x_697_);
lean_dec(v_key_692_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_entries_701_);
lean_ctor_set(v___x_738_, 1, v___x_728_);
return v___x_738_;
}
}
}
}
}
default: 
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_val_754_; lean_object* v___y_756_; lean_object* v_i_757_; lean_object* v___y_766_; lean_object* v_size_777_; lean_object* v_keyArray_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_752_ = lean_box(0);
v___x_753_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_699_, v___x_752_);
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec(v___x_753_);
v_size_777_ = lean_ctor_get(v_indexes_695_, 0);
v_keyArray_778_ = lean_ctor_get(v_indexes_695_, 1);
v___x_779_ = lean_unsigned_to_nat(1u);
v___x_780_ = lean_nat_add(v_size_777_, v___x_779_);
v___x_781_ = lean_array_get_size(v_keyArray_778_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec(v___x_780_);
lean_inc_ref(v_inst_690_);
lean_inc_ref(v_inst_689_);
v___x_783_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_689_, v_inst_690_, v_indexes_695_);
v___y_766_ = v___x_783_;
goto v___jp_765_;
}
else
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_784_ = lean_unsigned_to_nat(4u);
v___x_785_ = lean_nat_mul(v___x_780_, v___x_784_);
lean_dec(v___x_780_);
v___x_786_ = lean_unsigned_to_nat(3u);
v___x_787_ = lean_nat_mul(v___x_781_, v___x_786_);
v___x_788_ = lean_nat_dec_le(v___x_785_, v___x_787_);
lean_dec(v___x_787_);
lean_dec(v___x_785_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_inc_ref(v_inst_690_);
lean_inc_ref(v_inst_689_);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_689_, v_inst_690_, v_indexes_695_);
v___y_766_ = v___x_789_;
goto v___jp_765_;
}
else
{
v___y_766_ = v_indexes_695_;
goto v___jp_765_;
}
}
v___jp_755_:
{
lean_object* v_size_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v_size_758_ = lean_ctor_get(v___y_756_, 0);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v_size_758_, v___x_759_);
v___x_761_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_756_, v___x_760_, v_i_757_, v_key_692_, v_val_754_);
lean_dec(v_i_757_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_761_);
lean_ctor_set(v___x_697_, 0, v_entries_701_);
v___x_763_ = v___x_697_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_entries_701_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
v___jp_765_:
{
lean_object* v___x_767_; 
lean_inc(v_key_692_);
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_689_, v_inst_690_, v___y_766_, v_key_692_);
switch(lean_obj_tag(v___x_767_))
{
case 0:
{
lean_object* v_index_768_; lean_object* v_size_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_del_object(v___x_697_);
v_index_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_768_);
lean_dec_ref_known(v___x_767_, 3);
v_size_769_ = lean_ctor_get(v___y_766_, 0);
lean_inc(v_size_769_);
v___x_770_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_766_, v_size_769_, v_index_768_, v_key_692_, v_val_754_);
lean_dec(v_index_768_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_entries_701_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
return v___x_771_;
}
case 1:
{
lean_object* v_index_772_; 
v_index_772_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_index_772_);
lean_dec_ref_known(v___x_767_, 1);
v___y_756_ = v___y_766_;
v_i_757_ = v_index_772_;
goto v___jp_755_;
}
default: 
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_766_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_index_775_; 
v_index_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_774_, 1);
v___y_756_ = v___y_766_;
v_i_757_ = v_index_775_;
goto v___jp_755_;
}
else
{
lean_object* v___x_776_; 
lean_dec(v_val_754_);
lean_del_object(v___x_697_);
lean_dec(v_key_692_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_entries_701_);
lean_ctor_set(v___x_776_, 1, v___y_766_);
return v___x_776_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insert(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_map_797_, lean_object* v_key_798_, lean_object* v_value_799_){
_start:
{
lean_object* v_entries_800_; lean_object* v_indexes_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_896_; 
v_entries_800_ = lean_ctor_get(v_map_797_, 0);
v_indexes_801_ = lean_ctor_get(v_map_797_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_map_797_);
if (v_isSharedCheck_896_ == 0)
{
v___x_803_ = v_map_797_;
v_isShared_804_ = v_isSharedCheck_896_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_indexes_801_);
lean_inc(v_entries_800_);
lean_dec(v_map_797_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_896_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_i_805_; lean_object* v___x_806_; lean_object* v_entries_807_; lean_object* v___x_808_; 
v_i_805_ = lean_array_get_size(v_entries_800_);
lean_inc_n(v_key_798_, 2);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_key_798_);
lean_ctor_set(v___x_806_, 1, v_value_799_);
v_entries_807_ = lean_array_push(v_entries_800_, v___x_806_);
lean_inc_ref(v_inst_794_);
lean_inc_ref(v_inst_793_);
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_793_, v_inst_794_, v_indexes_801_, v_key_798_);
switch(lean_obj_tag(v___x_808_))
{
case 0:
{
lean_object* v_index_809_; lean_object* v_value_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_val_813_; lean_object* v_size_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_inst_793_);
v_index_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_index_809_);
v_value_810_ = lean_ctor_get(v___x_808_, 2);
lean_inc(v_value_810_);
lean_dec_ref_known(v___x_808_, 3);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v_value_810_);
v___x_812_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_805_, v___x_811_);
v_val_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_813_);
lean_dec(v___x_812_);
v_size_814_ = lean_ctor_get(v_indexes_801_, 0);
lean_inc(v_size_814_);
v___x_815_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_801_, v_size_814_, v_index_809_, v_key_798_, v_val_813_);
lean_dec(v_index_809_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_815_);
lean_ctor_set(v___x_803_, 0, v_entries_807_);
v___x_817_ = v___x_803_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_entries_807_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
case 1:
{
lean_object* v_index_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v_val_822_; lean_object* v___y_824_; lean_object* v_i_825_; lean_object* v_size_845_; lean_object* v_keyArray_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_index_819_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_index_819_);
lean_dec_ref_known(v___x_808_, 1);
v___x_820_ = lean_box(0);
v___x_821_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_805_, v___x_820_);
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec(v___x_821_);
v_size_845_ = lean_ctor_get(v_indexes_801_, 0);
v_keyArray_846_ = lean_ctor_get(v_indexes_801_, 1);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_size_845_, v___x_847_);
v___x_849_ = lean_array_get_size(v_keyArray_846_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec(v___x_848_);
lean_dec(v_index_819_);
goto v___jp_833_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_851_ = lean_unsigned_to_nat(4u);
v___x_852_ = lean_nat_mul(v___x_848_, v___x_851_);
v___x_853_ = lean_unsigned_to_nat(3u);
v___x_854_ = lean_nat_mul(v___x_849_, v___x_853_);
v___x_855_ = lean_nat_dec_le(v___x_852_, v___x_854_);
lean_dec(v___x_854_);
lean_dec(v___x_852_);
if (v___x_855_ == 0)
{
lean_dec(v___x_848_);
lean_dec(v_index_819_);
goto v___jp_833_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
lean_del_object(v___x_803_);
lean_dec_ref(v_inst_794_);
lean_dec_ref(v_inst_793_);
v___x_856_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_801_, v___x_848_, v_index_819_, v_key_798_, v_val_822_);
lean_dec(v_index_819_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_entries_807_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
return v___x_857_;
}
}
v___jp_823_:
{
lean_object* v_size_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v_size_826_ = lean_ctor_get(v___y_824_, 0);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_size_826_, v___x_827_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_824_, v___x_828_, v_i_825_, v_key_798_, v_val_822_);
lean_dec(v_i_825_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_829_);
lean_ctor_set(v___x_803_, 0, v_entries_807_);
v___x_831_ = v___x_803_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_entries_807_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
v___jp_833_:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc_ref(v_inst_794_);
lean_inc_ref(v_inst_793_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_793_, v_inst_794_, v_indexes_801_);
lean_inc(v_key_798_);
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_793_, v_inst_794_, v___x_834_, v_key_798_);
switch(lean_obj_tag(v___x_835_))
{
case 0:
{
lean_object* v_index_836_; lean_object* v_size_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_del_object(v___x_803_);
v_index_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_836_);
lean_dec_ref_known(v___x_835_, 3);
v_size_837_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_size_837_);
v___x_838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_834_, v_size_837_, v_index_836_, v_key_798_, v_val_822_);
lean_dec(v_index_836_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_entries_807_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
case 1:
{
lean_object* v_index_840_; 
v_index_840_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_index_840_);
lean_dec_ref_known(v___x_835_, 1);
v___y_824_ = v___x_834_;
v_i_825_ = v_index_840_;
goto v___jp_823_;
}
default: 
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_834_, v___x_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_index_843_; 
v_index_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_index_843_);
lean_dec_ref_known(v___x_842_, 1);
v___y_824_ = v___x_834_;
v_i_825_ = v_index_843_;
goto v___jp_823_;
}
else
{
lean_object* v___x_844_; 
lean_dec(v_val_822_);
lean_del_object(v___x_803_);
lean_dec(v_key_798_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v_entries_807_);
lean_ctor_set(v___x_844_, 1, v___x_834_);
return v___x_844_;
}
}
}
}
}
default: 
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v_val_860_; lean_object* v___y_862_; lean_object* v_i_863_; lean_object* v___y_872_; lean_object* v_size_883_; lean_object* v_keyArray_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_858_ = lean_box(0);
v___x_859_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_805_, v___x_858_);
v_val_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_val_860_);
lean_dec(v___x_859_);
v_size_883_ = lean_ctor_get(v_indexes_801_, 0);
v_keyArray_884_ = lean_ctor_get(v_indexes_801_, 1);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_add(v_size_883_, v___x_885_);
v___x_887_ = lean_array_get_size(v_keyArray_884_);
v___x_888_ = lean_nat_dec_lt(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v___x_886_);
lean_inc_ref(v_inst_794_);
lean_inc_ref(v_inst_793_);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_793_, v_inst_794_, v_indexes_801_);
v___y_872_ = v___x_889_;
goto v___jp_871_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_890_ = lean_unsigned_to_nat(4u);
v___x_891_ = lean_nat_mul(v___x_886_, v___x_890_);
lean_dec(v___x_886_);
v___x_892_ = lean_unsigned_to_nat(3u);
v___x_893_ = lean_nat_mul(v___x_887_, v___x_892_);
v___x_894_ = lean_nat_dec_le(v___x_891_, v___x_893_);
lean_dec(v___x_893_);
lean_dec(v___x_891_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_inc_ref(v_inst_794_);
lean_inc_ref(v_inst_793_);
v___x_895_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_793_, v_inst_794_, v_indexes_801_);
v___y_872_ = v___x_895_;
goto v___jp_871_;
}
else
{
v___y_872_ = v_indexes_801_;
goto v___jp_871_;
}
}
v___jp_861_:
{
lean_object* v_size_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v_size_864_ = lean_ctor_get(v___y_862_, 0);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v_size_864_, v___x_865_);
v___x_867_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_862_, v___x_866_, v_i_863_, v_key_798_, v_val_860_);
lean_dec(v_i_863_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_867_);
lean_ctor_set(v___x_803_, 0, v_entries_807_);
v___x_869_ = v___x_803_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_entries_807_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
v___jp_871_:
{
lean_object* v___x_873_; 
lean_inc(v_key_798_);
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_793_, v_inst_794_, v___y_872_, v_key_798_);
switch(lean_obj_tag(v___x_873_))
{
case 0:
{
lean_object* v_index_874_; lean_object* v_size_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_del_object(v___x_803_);
v_index_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_index_874_);
lean_dec_ref_known(v___x_873_, 3);
v_size_875_ = lean_ctor_get(v___y_872_, 0);
lean_inc(v_size_875_);
v___x_876_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_872_, v_size_875_, v_index_874_, v_key_798_, v_val_860_);
lean_dec(v_index_874_);
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_entries_807_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
return v___x_877_;
}
case 1:
{
lean_object* v_index_878_; 
v_index_878_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_index_878_);
lean_dec_ref_known(v___x_873_, 1);
v___y_862_ = v___y_872_;
v_i_863_ = v_index_878_;
goto v___jp_861_;
}
default: 
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_872_, v___x_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_index_881_; 
v_index_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_index_881_);
lean_dec_ref_known(v___x_880_, 1);
v___y_862_ = v___y_872_;
v_i_863_ = v_index_881_;
goto v___jp_861_;
}
else
{
lean_object* v___x_882_; 
lean_dec(v_val_860_);
lean_del_object(v___x_803_);
lean_dec(v_key_798_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_entries_807_);
lean_ctor_set(v___x_882_, 1, v___y_872_);
return v___x_882_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1(lean_object* v_key_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_x1_900_, lean_object* v_x2_901_){
_start:
{
lean_object* v_entries_902_; lean_object* v_indexes_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_998_; 
v_entries_902_ = lean_ctor_get(v_x1_900_, 0);
v_indexes_903_ = lean_ctor_get(v_x1_900_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x1_900_);
if (v_isSharedCheck_998_ == 0)
{
v___x_905_ = v_x1_900_;
v_isShared_906_ = v_isSharedCheck_998_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_indexes_903_);
lean_inc(v_entries_902_);
lean_dec(v_x1_900_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_998_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_i_907_; lean_object* v___x_908_; lean_object* v_entries_909_; lean_object* v___x_910_; 
v_i_907_ = lean_array_get_size(v_entries_902_);
lean_inc_n(v_key_897_, 2);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_key_897_);
lean_ctor_set(v___x_908_, 1, v_x2_901_);
v_entries_909_ = lean_array_push(v_entries_902_, v___x_908_);
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_inst_898_);
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_898_, v_inst_899_, v_indexes_903_, v_key_897_);
switch(lean_obj_tag(v___x_910_))
{
case 0:
{
lean_object* v_index_911_; lean_object* v_value_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_val_915_; lean_object* v_size_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
lean_dec_ref(v_inst_899_);
lean_dec_ref(v_inst_898_);
v_index_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_index_911_);
v_value_912_ = lean_ctor_get(v___x_910_, 2);
lean_inc(v_value_912_);
lean_dec_ref_known(v___x_910_, 3);
v___x_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_913_, 0, v_value_912_);
v___x_914_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_907_, v___x_913_);
v_val_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_val_915_);
lean_dec(v___x_914_);
v_size_916_ = lean_ctor_get(v_indexes_903_, 0);
lean_inc(v_size_916_);
v___x_917_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_903_, v_size_916_, v_index_911_, v_key_897_, v_val_915_);
lean_dec(v_index_911_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_917_);
lean_ctor_set(v___x_905_, 0, v_entries_909_);
v___x_919_ = v___x_905_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_entries_909_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
case 1:
{
lean_object* v_index_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_val_924_; lean_object* v___y_926_; lean_object* v_i_927_; lean_object* v_size_947_; lean_object* v_keyArray_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_index_921_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_index_921_);
lean_dec_ref_known(v___x_910_, 1);
v___x_922_ = lean_box(0);
v___x_923_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_907_, v___x_922_);
v_val_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_val_924_);
lean_dec(v___x_923_);
v_size_947_ = lean_ctor_get(v_indexes_903_, 0);
v_keyArray_948_ = lean_ctor_get(v_indexes_903_, 1);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_size_947_, v___x_949_);
v___x_951_ = lean_array_get_size(v_keyArray_948_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec(v___x_950_);
lean_dec(v_index_921_);
goto v___jp_935_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_953_ = lean_unsigned_to_nat(4u);
v___x_954_ = lean_nat_mul(v___x_950_, v___x_953_);
v___x_955_ = lean_unsigned_to_nat(3u);
v___x_956_ = lean_nat_mul(v___x_951_, v___x_955_);
v___x_957_ = lean_nat_dec_le(v___x_954_, v___x_956_);
lean_dec(v___x_956_);
lean_dec(v___x_954_);
if (v___x_957_ == 0)
{
lean_dec(v___x_950_);
lean_dec(v_index_921_);
goto v___jp_935_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_del_object(v___x_905_);
lean_dec_ref(v_inst_899_);
lean_dec_ref(v_inst_898_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_903_, v___x_950_, v_index_921_, v_key_897_, v_val_924_);
lean_dec(v_index_921_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v_entries_909_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
return v___x_959_;
}
}
v___jp_925_:
{
lean_object* v_size_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v_size_928_ = lean_ctor_get(v___y_926_, 0);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_add(v_size_928_, v___x_929_);
v___x_931_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_926_, v___x_930_, v_i_927_, v_key_897_, v_val_924_);
lean_dec(v_i_927_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_931_);
lean_ctor_set(v___x_905_, 0, v_entries_909_);
v___x_933_ = v___x_905_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_entries_909_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
v___jp_935_:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_inst_898_);
v___x_936_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_898_, v_inst_899_, v_indexes_903_);
lean_inc(v_key_897_);
v___x_937_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_898_, v_inst_899_, v___x_936_, v_key_897_);
switch(lean_obj_tag(v___x_937_))
{
case 0:
{
lean_object* v_index_938_; lean_object* v_size_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_del_object(v___x_905_);
v_index_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_index_938_);
lean_dec_ref_known(v___x_937_, 3);
v_size_939_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_size_939_);
v___x_940_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_936_, v_size_939_, v_index_938_, v_key_897_, v_val_924_);
lean_dec(v_index_938_);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v_entries_909_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
return v___x_941_;
}
case 1:
{
lean_object* v_index_942_; 
v_index_942_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_index_942_);
lean_dec_ref_known(v___x_937_, 1);
v___y_926_ = v___x_936_;
v_i_927_ = v_index_942_;
goto v___jp_925_;
}
default: 
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_936_, v___x_943_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_index_945_; 
v_index_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_index_945_);
lean_dec_ref_known(v___x_944_, 1);
v___y_926_ = v___x_936_;
v_i_927_ = v_index_945_;
goto v___jp_925_;
}
else
{
lean_object* v___x_946_; 
lean_dec(v_val_924_);
lean_del_object(v___x_905_);
lean_dec(v_key_897_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_entries_909_);
lean_ctor_set(v___x_946_, 1, v___x_936_);
return v___x_946_;
}
}
}
}
}
default: 
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_val_962_; lean_object* v___y_964_; lean_object* v_i_965_; lean_object* v___y_974_; lean_object* v_size_985_; lean_object* v_keyArray_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_960_ = lean_box(0);
v___x_961_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_907_, v___x_960_);
v_val_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_val_962_);
lean_dec(v___x_961_);
v_size_985_ = lean_ctor_get(v_indexes_903_, 0);
v_keyArray_986_ = lean_ctor_get(v_indexes_903_, 1);
v___x_987_ = lean_unsigned_to_nat(1u);
v___x_988_ = lean_nat_add(v_size_985_, v___x_987_);
v___x_989_ = lean_array_get_size(v_keyArray_986_);
v___x_990_ = lean_nat_dec_lt(v___x_988_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v___x_988_);
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_inst_898_);
v___x_991_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_898_, v_inst_899_, v_indexes_903_);
v___y_974_ = v___x_991_;
goto v___jp_973_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_992_ = lean_unsigned_to_nat(4u);
v___x_993_ = lean_nat_mul(v___x_988_, v___x_992_);
lean_dec(v___x_988_);
v___x_994_ = lean_unsigned_to_nat(3u);
v___x_995_ = lean_nat_mul(v___x_989_, v___x_994_);
v___x_996_ = lean_nat_dec_le(v___x_993_, v___x_995_);
lean_dec(v___x_995_);
lean_dec(v___x_993_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_inst_898_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_898_, v_inst_899_, v_indexes_903_);
v___y_974_ = v___x_997_;
goto v___jp_973_;
}
else
{
v___y_974_ = v_indexes_903_;
goto v___jp_973_;
}
}
v___jp_963_:
{
lean_object* v_size_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v_size_966_ = lean_ctor_get(v___y_964_, 0);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_size_966_, v___x_967_);
v___x_969_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_964_, v___x_968_, v_i_965_, v_key_897_, v_val_962_);
lean_dec(v_i_965_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 1, v___x_969_);
lean_ctor_set(v___x_905_, 0, v_entries_909_);
v___x_971_ = v___x_905_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_entries_909_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
v___jp_973_:
{
lean_object* v___x_975_; 
lean_inc(v_key_897_);
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_898_, v_inst_899_, v___y_974_, v_key_897_);
switch(lean_obj_tag(v___x_975_))
{
case 0:
{
lean_object* v_index_976_; lean_object* v_size_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_del_object(v___x_905_);
v_index_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_976_);
lean_dec_ref_known(v___x_975_, 3);
v_size_977_ = lean_ctor_get(v___y_974_, 0);
lean_inc(v_size_977_);
v___x_978_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_974_, v_size_977_, v_index_976_, v_key_897_, v_val_962_);
lean_dec(v_index_976_);
v___x_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_979_, 0, v_entries_909_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
return v___x_979_;
}
case 1:
{
lean_object* v_index_980_; 
v_index_980_ = lean_ctor_get(v___x_975_, 0);
lean_inc(v_index_980_);
lean_dec_ref_known(v___x_975_, 1);
v___y_964_ = v___y_974_;
v_i_965_ = v_index_980_;
goto v___jp_963_;
}
default: 
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_974_, v___x_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_index_983_; 
v_index_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_index_983_);
lean_dec_ref_known(v___x_982_, 1);
v___y_964_ = v___y_974_;
v_i_965_ = v_index_983_;
goto v___jp_963_;
}
else
{
lean_object* v___x_984_; 
lean_dec(v_val_962_);
lean_del_object(v___x_905_);
lean_dec(v_key_897_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_entries_909_);
lean_ctor_set(v___x_984_, 1, v___y_974_);
return v___x_984_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany___redArg(lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_map_1001_, lean_object* v_key_1002_, lean_object* v_values_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_values_1003_);
v___x_1006_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1007_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v_values_1003_);
lean_dec(v_key_1002_);
lean_dec_ref(v_inst_1000_);
lean_dec_ref(v_inst_999_);
return v_map_1001_;
}
else
{
lean_object* v___f_1008_; uint8_t v___x_1009_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1008_, 0, v_key_1002_);
lean_closure_set(v___f_1008_, 1, v_inst_999_);
lean_closure_set(v___f_1008_, 2, v_inst_1000_);
v___x_1009_ = lean_nat_dec_le(v___x_1005_, v___x_1005_);
if (v___x_1009_ == 0)
{
if (v___x_1007_ == 0)
{
lean_dec_ref(v___f_1008_);
lean_dec_ref(v_values_1003_);
return v_map_1001_;
}
else
{
size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v___x_1010_ = ((size_t)0ULL);
v___x_1011_ = lean_usize_of_nat(v___x_1005_);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1006_, v___f_1008_, v_values_1003_, v___x_1010_, v___x_1011_, v_map_1001_);
return v___x_1012_;
}
}
else
{
size_t v___x_1013_; size_t v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = lean_usize_of_nat(v___x_1005_);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1006_, v___f_1008_, v_values_1003_, v___x_1013_, v___x_1014_, v_map_1001_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_insertMany(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_map_1022_, lean_object* v_key_1023_, lean_object* v_values_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_array_get_size(v_values_1024_);
v___x_1027_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1028_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v_values_1024_);
lean_dec(v_key_1023_);
lean_dec_ref(v_inst_1019_);
lean_dec_ref(v_inst_1018_);
return v_map_1022_;
}
else
{
lean_object* v___f_1029_; uint8_t v___x_1030_; 
v___f_1029_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_insertMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1029_, 0, v_key_1023_);
lean_closure_set(v___f_1029_, 1, v_inst_1018_);
lean_closure_set(v___f_1029_, 2, v_inst_1019_);
v___x_1030_ = lean_nat_dec_le(v___x_1026_, v___x_1026_);
if (v___x_1030_ == 0)
{
if (v___x_1028_ == 0)
{
lean_dec_ref(v___f_1029_);
lean_dec_ref(v_values_1024_);
return v_map_1022_;
}
else
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = lean_usize_of_nat(v___x_1026_);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1027_, v___f_1029_, v_values_1024_, v___x_1031_, v___x_1032_, v_map_1022_);
return v___x_1033_;
}
}
else
{
size_t v___x_1034_; size_t v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = lean_usize_of_nat(v___x_1026_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1027_, v___f_1029_, v_values_1024_, v___x_1034_, v___x_1035_, v_map_1022_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty(lean_object* v_00_u03b1_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Std_Internal_instInhabitedIndexMultiMap___closed__4, &l_Std_Internal_instInhabitedIndexMultiMap___closed__4_once, _init_l_Std_Internal_instInhabitedIndexMultiMap___closed__4);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_empty___boxed(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_Internal_IndexMultiMap_empty(v_00_u03b1_1042_, v_00_u03b2_1043_, v_inst_1044_, v_inst_1045_);
lean_dec_ref(v_inst_1045_);
lean_dec_ref(v_inst_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1(lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_acc_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v_fst_1051_; lean_object* v_entries_1052_; lean_object* v_indexes_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1147_; 
v_fst_1051_ = lean_ctor_get(v_x_1050_, 0);
lean_inc(v_fst_1051_);
v_entries_1052_ = lean_ctor_get(v_acc_1049_, 0);
v_indexes_1053_ = lean_ctor_get(v_acc_1049_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_acc_1049_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1055_ = v_acc_1049_;
v_isShared_1056_ = v_isSharedCheck_1147_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_indexes_1053_);
lean_inc(v_entries_1052_);
lean_dec(v_acc_1049_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1147_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_i_1057_; lean_object* v_entries_1058_; lean_object* v___x_1059_; 
v_i_1057_ = lean_array_get_size(v_entries_1052_);
v_entries_1058_ = lean_array_push(v_entries_1052_, v_x_1050_);
lean_inc(v_fst_1051_);
lean_inc_ref(v_inst_1048_);
lean_inc_ref(v_inst_1047_);
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1047_, v_inst_1048_, v_indexes_1053_, v_fst_1051_);
switch(lean_obj_tag(v___x_1059_))
{
case 0:
{
lean_object* v_index_1060_; lean_object* v_value_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v_val_1064_; lean_object* v_size_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1047_);
v_index_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_index_1060_);
v_value_1061_ = lean_ctor_get(v___x_1059_, 2);
lean_inc(v_value_1061_);
lean_dec_ref_known(v___x_1059_, 3);
v___x_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_value_1061_);
v___x_1063_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1057_, v___x_1062_);
v_val_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_val_1064_);
lean_dec(v___x_1063_);
v_size_1065_ = lean_ctor_get(v_indexes_1053_, 0);
lean_inc(v_size_1065_);
v___x_1066_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1053_, v_size_1065_, v_index_1060_, v_fst_1051_, v_val_1064_);
lean_dec(v_index_1060_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1066_);
lean_ctor_set(v___x_1055_, 0, v_entries_1058_);
v___x_1068_ = v___x_1055_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_entries_1058_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
case 1:
{
lean_object* v_index_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_val_1073_; lean_object* v___y_1075_; lean_object* v_i_1076_; lean_object* v_size_1096_; lean_object* v_keyArray_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_index_1070_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_index_1070_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1071_ = lean_box(0);
v___x_1072_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1057_, v___x_1071_);
v_val_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1073_);
lean_dec(v___x_1072_);
v_size_1096_ = lean_ctor_get(v_indexes_1053_, 0);
v_keyArray_1097_ = lean_ctor_get(v_indexes_1053_, 1);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_size_1096_, v___x_1098_);
v___x_1100_ = lean_array_get_size(v_keyArray_1097_);
v___x_1101_ = lean_nat_dec_lt(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec(v___x_1099_);
lean_dec(v_index_1070_);
goto v___jp_1084_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1102_ = lean_unsigned_to_nat(4u);
v___x_1103_ = lean_nat_mul(v___x_1099_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(3u);
v___x_1105_ = lean_nat_mul(v___x_1100_, v___x_1104_);
v___x_1106_ = lean_nat_dec_le(v___x_1103_, v___x_1105_);
lean_dec(v___x_1105_);
lean_dec(v___x_1103_);
if (v___x_1106_ == 0)
{
lean_dec(v___x_1099_);
lean_dec(v_index_1070_);
goto v___jp_1084_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_1055_);
lean_dec_ref(v_inst_1048_);
lean_dec_ref(v_inst_1047_);
v___x_1107_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1053_, v___x_1099_, v_index_1070_, v_fst_1051_, v_val_1073_);
lean_dec(v_index_1070_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_entries_1058_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
return v___x_1108_;
}
}
v___jp_1074_:
{
lean_object* v_size_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v_size_1077_ = lean_ctor_get(v___y_1075_, 0);
v___x_1078_ = lean_unsigned_to_nat(1u);
v___x_1079_ = lean_nat_add(v_size_1077_, v___x_1078_);
v___x_1080_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1075_, v___x_1079_, v_i_1076_, v_fst_1051_, v_val_1073_);
lean_dec(v_i_1076_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1080_);
lean_ctor_set(v___x_1055_, 0, v_entries_1058_);
v___x_1082_ = v___x_1055_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_entries_1058_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
v___jp_1084_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_inc_ref(v_inst_1048_);
lean_inc_ref(v_inst_1047_);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1047_, v_inst_1048_, v_indexes_1053_);
lean_inc(v_fst_1051_);
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1047_, v_inst_1048_, v___x_1085_, v_fst_1051_);
switch(lean_obj_tag(v___x_1086_))
{
case 0:
{
lean_object* v_index_1087_; lean_object* v_size_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_del_object(v___x_1055_);
v_index_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_index_1087_);
lean_dec_ref_known(v___x_1086_, 3);
v_size_1088_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_size_1088_);
v___x_1089_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1085_, v_size_1088_, v_index_1087_, v_fst_1051_, v_val_1073_);
lean_dec(v_index_1087_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_entries_1058_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
return v___x_1090_;
}
case 1:
{
lean_object* v_index_1091_; 
v_index_1091_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_index_1091_);
lean_dec_ref_known(v___x_1086_, 1);
v___y_1075_ = v___x_1085_;
v_i_1076_ = v_index_1091_;
goto v___jp_1074_;
}
default: 
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1085_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_index_1094_; 
v_index_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_index_1094_);
lean_dec_ref_known(v___x_1093_, 1);
v___y_1075_ = v___x_1085_;
v_i_1076_ = v_index_1094_;
goto v___jp_1074_;
}
else
{
lean_object* v___x_1095_; 
lean_dec(v_val_1073_);
lean_del_object(v___x_1055_);
lean_dec(v_fst_1051_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_entries_1058_);
lean_ctor_set(v___x_1095_, 1, v___x_1085_);
return v___x_1095_;
}
}
}
}
}
default: 
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_val_1111_; lean_object* v___y_1113_; lean_object* v_i_1114_; lean_object* v___y_1123_; lean_object* v_size_1134_; lean_object* v_keyArray_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1057_, v___x_1109_);
v_val_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_val_1111_);
lean_dec(v___x_1110_);
v_size_1134_ = lean_ctor_get(v_indexes_1053_, 0);
v_keyArray_1135_ = lean_ctor_get(v_indexes_1053_, 1);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_size_1134_, v___x_1136_);
v___x_1138_ = lean_array_get_size(v_keyArray_1135_);
v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec(v___x_1137_);
lean_inc_ref(v_inst_1048_);
lean_inc_ref(v_inst_1047_);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1047_, v_inst_1048_, v_indexes_1053_);
v___y_1123_ = v___x_1140_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1141_ = lean_unsigned_to_nat(4u);
v___x_1142_ = lean_nat_mul(v___x_1137_, v___x_1141_);
lean_dec(v___x_1137_);
v___x_1143_ = lean_unsigned_to_nat(3u);
v___x_1144_ = lean_nat_mul(v___x_1138_, v___x_1143_);
v___x_1145_ = lean_nat_dec_le(v___x_1142_, v___x_1144_);
lean_dec(v___x_1144_);
lean_dec(v___x_1142_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_inc_ref(v_inst_1048_);
lean_inc_ref(v_inst_1047_);
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1047_, v_inst_1048_, v_indexes_1053_);
v___y_1123_ = v___x_1146_;
goto v___jp_1122_;
}
else
{
v___y_1123_ = v_indexes_1053_;
goto v___jp_1122_;
}
}
v___jp_1112_:
{
lean_object* v_size_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_size_1115_ = lean_ctor_get(v___y_1113_, 0);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_size_1115_, v___x_1116_);
v___x_1118_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1113_, v___x_1117_, v_i_1114_, v_fst_1051_, v_val_1111_);
lean_dec(v_i_1114_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1118_);
lean_ctor_set(v___x_1055_, 0, v_entries_1058_);
v___x_1120_ = v___x_1055_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_entries_1058_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; 
lean_inc(v_fst_1051_);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1047_, v_inst_1048_, v___y_1123_, v_fst_1051_);
switch(lean_obj_tag(v___x_1124_))
{
case 0:
{
lean_object* v_index_1125_; lean_object* v_size_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_del_object(v___x_1055_);
v_index_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_index_1125_);
lean_dec_ref_known(v___x_1124_, 3);
v_size_1126_ = lean_ctor_get(v___y_1123_, 0);
lean_inc(v_size_1126_);
v___x_1127_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1123_, v_size_1126_, v_index_1125_, v_fst_1051_, v_val_1111_);
lean_dec(v_index_1125_);
v___x_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1128_, 0, v_entries_1058_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
return v___x_1128_;
}
case 1:
{
lean_object* v_index_1129_; 
v_index_1129_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_index_1129_);
lean_dec_ref_known(v___x_1124_, 1);
v___y_1113_ = v___y_1123_;
v_i_1114_ = v_index_1129_;
goto v___jp_1112_;
}
default: 
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1123_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_index_1132_; 
v_index_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_index_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___y_1113_ = v___y_1123_;
v_i_1114_ = v_index_1132_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_val_1111_);
lean_del_object(v___x_1055_);
lean_dec(v_fst_1051_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_entries_1058_);
lean_ctor_set(v___x_1133_, 1, v___y_1123_);
return v___x_1133_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList___redArg(lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_pairs_1150_){
_start:
{
lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_inc_ref(v_inst_1149_);
lean_inc_ref(v_inst_1148_);
v___f_1151_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_ofList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1151_, 0, v_inst_1148_);
lean_closure_set(v___f_1151_, 1, v_inst_1149_);
v___x_1152_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1148_, v_inst_1149_);
lean_dec_ref(v_inst_1149_);
lean_dec_ref(v_inst_1148_);
v___x_1153_ = l_List_foldl___redArg(v___f_1151_, v___x_1152_, v_pairs_1150_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_ofList(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_pairs_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Std_Internal_IndexMultiMap_ofList___redArg(v_inst_1156_, v_inst_1157_, v_pairs_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains___redArg(lean_object* v_inst_1162_, lean_object* v_inst_1163_, lean_object* v_map_1164_, lean_object* v_key_1165_){
_start:
{
lean_object* v_indexes_1166_; uint8_t v___x_1167_; 
v_indexes_1166_ = lean_ctor_get(v_map_1164_, 1);
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1162_, v_inst_1163_, v_indexes_1166_, v_key_1165_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___redArg___boxed(lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_map_1170_, lean_object* v_key_1171_){
_start:
{
uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_res_1172_ = l_Std_Internal_IndexMultiMap_contains___redArg(v_inst_1168_, v_inst_1169_, v_map_1170_, v_key_1171_);
lean_dec_ref(v_map_1170_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_contains(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_map_1178_, lean_object* v_key_1179_){
_start:
{
lean_object* v_indexes_1180_; uint8_t v___x_1181_; 
v_indexes_1180_ = lean_ctor_get(v_map_1178_, 1);
v___x_1181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1176_, v_inst_1177_, v_indexes_1180_, v_key_1179_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_contains___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_map_1186_, lean_object* v_key_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Std_Internal_IndexMultiMap_contains(v_00_u03b1_1182_, v_00_u03b2_1183_, v_inst_1184_, v_inst_1185_, v_map_1186_, v_key_1187_);
lean_dec_ref(v_map_1186_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg___lam__1(lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_key_1192_, lean_object* v_f_1193_, lean_object* v_x1_1194_, lean_object* v_x2_1195_){
_start:
{
lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1312_; 
v_fst_1196_ = lean_ctor_get(v_x2_1195_, 0);
v_snd_1197_ = lean_ctor_get(v_x2_1195_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v_x2_1195_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1199_ = v_x2_1195_;
v_isShared_1200_ = v_isSharedCheck_1312_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_snd_1197_);
lean_inc(v_fst_1196_);
lean_dec(v_x2_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1312_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v_i_1205_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v_i_1229_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1251_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_inc_ref(v_inst_1190_);
lean_inc(v_fst_1196_);
v___x_1309_ = lean_apply_2(v_inst_1190_, v_fst_1196_, v_key_1192_);
v___x_1310_ = lean_unbox(v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec(v_f_1193_);
v___y_1251_ = v_snd_1197_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_apply_1(v_f_1193_, v_snd_1197_);
v___y_1251_ = v___x_1311_;
goto v___jp_1250_;
}
v___jp_1201_:
{
lean_object* v_size_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_size_1206_ = lean_ctor_get(v___y_1203_, 0);
v___x_1207_ = lean_unsigned_to_nat(1u);
v___x_1208_ = lean_nat_add(v_size_1206_, v___x_1207_);
v___x_1209_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1203_, v___x_1208_, v_i_1205_, v_fst_1196_, v___y_1202_);
lean_dec(v_i_1205_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___y_1204_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
return v___x_1210_;
}
v___jp_1211_:
{
lean_object* v___x_1215_; 
lean_inc(v_fst_1196_);
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1190_, v_inst_1191_, v___y_1214_, v_fst_1196_);
switch(lean_obj_tag(v___x_1215_))
{
case 0:
{
lean_object* v_index_1216_; lean_object* v_size_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_index_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_index_1216_);
lean_dec_ref_known(v___x_1215_, 3);
v_size_1217_ = lean_ctor_get(v___y_1214_, 0);
lean_inc(v_size_1217_);
v___x_1218_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1214_, v_size_1217_, v_index_1216_, v_fst_1196_, v___y_1212_);
lean_dec(v_index_1216_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___y_1213_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
case 1:
{
lean_object* v_index_1220_; 
v_index_1220_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_index_1220_);
lean_dec_ref_known(v___x_1215_, 1);
v___y_1202_ = v___y_1212_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1213_;
v_i_1205_ = v_index_1220_;
goto v___jp_1201_;
}
default: 
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1214_, v___x_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_index_1223_; 
v_index_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_index_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___y_1202_ = v___y_1212_;
v___y_1203_ = v___y_1214_;
v___y_1204_ = v___y_1213_;
v_i_1205_ = v_index_1223_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1224_; 
lean_dec_ref(v___y_1212_);
lean_dec(v_fst_1196_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1213_);
lean_ctor_set(v___x_1224_, 1, v___y_1214_);
return v___x_1224_;
}
}
}
}
v___jp_1225_:
{
lean_object* v_size_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_size_1230_ = lean_ctor_get(v___y_1226_, 0);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = lean_nat_add(v_size_1230_, v___x_1231_);
v___x_1233_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1226_, v___x_1232_, v_i_1229_, v_fst_1196_, v___y_1227_);
lean_dec(v_i_1229_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___y_1228_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
return v___x_1234_;
}
v___jp_1235_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_inc_ref(v_inst_1191_);
lean_inc_ref(v_inst_1190_);
v___x_1239_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1190_, v_inst_1191_, v___y_1237_);
lean_inc(v_fst_1196_);
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1190_, v_inst_1191_, v___x_1239_, v_fst_1196_);
switch(lean_obj_tag(v___x_1240_))
{
case 0:
{
lean_object* v_index_1241_; lean_object* v_size_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_index_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_index_1241_);
lean_dec_ref_known(v___x_1240_, 3);
v_size_1242_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_size_1242_);
v___x_1243_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1239_, v_size_1242_, v_index_1241_, v_fst_1196_, v___y_1236_);
lean_dec(v_index_1241_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1238_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
return v___x_1244_;
}
case 1:
{
lean_object* v_index_1245_; 
v_index_1245_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_index_1245_);
lean_dec_ref_known(v___x_1240_, 1);
v___y_1226_ = v___x_1239_;
v___y_1227_ = v___y_1236_;
v___y_1228_ = v___y_1238_;
v_i_1229_ = v_index_1245_;
goto v___jp_1225_;
}
default: 
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1239_, v___x_1246_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_index_1248_; 
v_index_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_index_1248_);
lean_dec_ref_known(v___x_1247_, 1);
v___y_1226_ = v___x_1239_;
v___y_1227_ = v___y_1236_;
v___y_1228_ = v___y_1238_;
v_i_1229_ = v_index_1248_;
goto v___jp_1225_;
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref(v___y_1236_);
lean_dec(v_fst_1196_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1238_);
lean_ctor_set(v___x_1249_, 1, v___x_1239_);
return v___x_1249_;
}
}
}
}
v___jp_1250_:
{
lean_object* v_entries_1252_; lean_object* v_indexes_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1308_; 
v_entries_1252_ = lean_ctor_get(v_x1_1194_, 0);
v_indexes_1253_ = lean_ctor_get(v_x1_1194_, 1);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_x1_1194_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1255_ = v_x1_1194_;
v_isShared_1256_ = v_isSharedCheck_1308_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_indexes_1253_);
lean_inc(v_entries_1252_);
lean_dec(v_x1_1194_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1308_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v_i_1257_; lean_object* v___x_1259_; 
v_i_1257_ = lean_array_get_size(v_entries_1252_);
lean_inc(v_fst_1196_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___y_1251_);
v___x_1259_ = v___x_1199_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_fst_1196_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___y_1251_);
v___x_1259_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v_entries_1260_; lean_object* v___x_1261_; 
v_entries_1260_ = lean_array_push(v_entries_1252_, v___x_1259_);
lean_inc(v_fst_1196_);
lean_inc_ref(v_inst_1191_);
lean_inc_ref(v_inst_1190_);
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1190_, v_inst_1191_, v_indexes_1253_, v_fst_1196_);
switch(lean_obj_tag(v___x_1261_))
{
case 0:
{
lean_object* v_index_1262_; lean_object* v_value_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_val_1266_; lean_object* v_size_1267_; lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_inst_1190_);
v_index_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_index_1262_);
v_value_1263_ = lean_ctor_get(v___x_1261_, 2);
lean_inc(v_value_1263_);
lean_dec_ref_known(v___x_1261_, 3);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_value_1263_);
v___x_1265_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1257_, v___x_1264_);
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec(v___x_1265_);
v_size_1267_ = lean_ctor_get(v_indexes_1253_, 0);
lean_inc(v_size_1267_);
v___x_1268_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1253_, v_size_1267_, v_index_1262_, v_fst_1196_, v_val_1266_);
lean_dec(v_index_1262_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1268_);
lean_ctor_set(v___x_1255_, 0, v_entries_1260_);
v___x_1270_ = v___x_1255_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_entries_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
case 1:
{
lean_object* v_index_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_val_1275_; lean_object* v_size_1276_; lean_object* v_keyArray_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_index_1272_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_index_1272_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1273_ = lean_box(0);
v___x_1274_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1257_, v___x_1273_);
v_val_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1275_);
lean_dec(v___x_1274_);
v_size_1276_ = lean_ctor_get(v_indexes_1253_, 0);
v_keyArray_1277_ = lean_ctor_get(v_indexes_1253_, 1);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_add(v_size_1276_, v___x_1278_);
v___x_1280_ = lean_array_get_size(v_keyArray_1277_);
v___x_1281_ = lean_nat_dec_lt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1279_);
lean_dec(v_index_1272_);
lean_del_object(v___x_1255_);
v___y_1236_ = v_val_1275_;
v___y_1237_ = v_indexes_1253_;
v___y_1238_ = v_entries_1260_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1282_ = lean_unsigned_to_nat(4u);
v___x_1283_ = lean_nat_mul(v___x_1279_, v___x_1282_);
v___x_1284_ = lean_unsigned_to_nat(3u);
v___x_1285_ = lean_nat_mul(v___x_1280_, v___x_1284_);
v___x_1286_ = lean_nat_dec_le(v___x_1283_, v___x_1285_);
lean_dec(v___x_1285_);
lean_dec(v___x_1283_);
if (v___x_1286_ == 0)
{
lean_dec(v___x_1279_);
lean_dec(v_index_1272_);
lean_del_object(v___x_1255_);
v___y_1236_ = v_val_1275_;
v___y_1237_ = v_indexes_1253_;
v___y_1238_ = v_entries_1260_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
lean_dec_ref(v_inst_1191_);
lean_dec_ref(v_inst_1190_);
v___x_1287_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1253_, v___x_1279_, v_index_1272_, v_fst_1196_, v_val_1275_);
lean_dec(v_index_1272_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1287_);
lean_ctor_set(v___x_1255_, 0, v_entries_1260_);
v___x_1289_ = v___x_1255_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_entries_1260_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
default: 
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_val_1293_; lean_object* v_size_1294_; lean_object* v_keyArray_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
lean_del_object(v___x_1255_);
v___x_1291_ = lean_box(0);
v___x_1292_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1257_, v___x_1291_);
v_val_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_val_1293_);
lean_dec(v___x_1292_);
v_size_1294_ = lean_ctor_get(v_indexes_1253_, 0);
v_keyArray_1295_ = lean_ctor_get(v_indexes_1253_, 1);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_add(v_size_1294_, v___x_1296_);
v___x_1298_ = lean_array_get_size(v_keyArray_1295_);
v___x_1299_ = lean_nat_dec_lt(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
lean_dec(v___x_1297_);
lean_inc_ref(v_inst_1191_);
lean_inc_ref(v_inst_1190_);
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1190_, v_inst_1191_, v_indexes_1253_);
v___y_1212_ = v_val_1293_;
v___y_1213_ = v_entries_1260_;
v___y_1214_ = v___x_1300_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1301_ = lean_unsigned_to_nat(4u);
v___x_1302_ = lean_nat_mul(v___x_1297_, v___x_1301_);
lean_dec(v___x_1297_);
v___x_1303_ = lean_unsigned_to_nat(3u);
v___x_1304_ = lean_nat_mul(v___x_1298_, v___x_1303_);
v___x_1305_ = lean_nat_dec_le(v___x_1302_, v___x_1304_);
lean_dec(v___x_1304_);
lean_dec(v___x_1302_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
lean_inc_ref(v_inst_1191_);
lean_inc_ref(v_inst_1190_);
v___x_1306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1190_, v_inst_1191_, v_indexes_1253_);
v___y_1212_ = v_val_1293_;
v___y_1213_ = v_entries_1260_;
v___y_1214_ = v___x_1306_;
goto v___jp_1211_;
}
else
{
v___y_1212_ = v_val_1293_;
v___y_1213_ = v_entries_1260_;
v___y_1214_ = v_indexes_1253_;
goto v___jp_1211_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update___redArg(lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_map_1315_, lean_object* v_key_1316_, lean_object* v_f_1317_){
_start:
{
uint8_t v___x_1318_; 
lean_inc(v_key_1316_);
lean_inc_ref(v_inst_1314_);
lean_inc_ref(v_inst_1313_);
v___x_1318_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1313_, v_inst_1314_, v_key_1316_, v_map_1315_);
if (v___x_1318_ == 0)
{
lean_dec(v_f_1317_);
lean_dec(v_key_1316_);
lean_dec_ref(v_inst_1314_);
lean_dec_ref(v_inst_1313_);
return v_map_1315_;
}
else
{
lean_object* v_entries_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_entries_1319_ = lean_ctor_get(v_map_1315_, 0);
lean_inc_ref(v_entries_1319_);
lean_dec_ref(v_map_1315_);
v___x_1320_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1313_, v_inst_1314_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_entries_1319_);
v___x_1323_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1324_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v_entries_1319_);
lean_dec(v_f_1317_);
lean_dec(v_key_1316_);
lean_dec_ref(v_inst_1314_);
lean_dec_ref(v_inst_1313_);
return v___x_1320_;
}
else
{
lean_object* v___f_1325_; uint8_t v___x_1326_; 
v___f_1325_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_1325_, 0, v_inst_1313_);
lean_closure_set(v___f_1325_, 1, v_inst_1314_);
lean_closure_set(v___f_1325_, 2, v_key_1316_);
lean_closure_set(v___f_1325_, 3, v_f_1317_);
v___x_1326_ = lean_nat_dec_le(v___x_1322_, v___x_1322_);
if (v___x_1326_ == 0)
{
if (v___x_1324_ == 0)
{
lean_dec_ref(v___f_1325_);
lean_dec_ref(v_entries_1319_);
return v___x_1320_;
}
else
{
size_t v___x_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1327_ = ((size_t)0ULL);
v___x_1328_ = lean_usize_of_nat(v___x_1322_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1323_, v___f_1325_, v_entries_1319_, v___x_1327_, v___x_1328_, v___x_1320_);
return v___x_1329_;
}
}
else
{
size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((size_t)0ULL);
v___x_1331_ = lean_usize_of_nat(v___x_1322_);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1323_, v___f_1325_, v_entries_1319_, v___x_1330_, v___x_1331_, v___x_1320_);
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_update(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_map_1339_, lean_object* v_key_1340_, lean_object* v_f_1341_){
_start:
{
uint8_t v___x_1342_; 
lean_inc(v_key_1340_);
lean_inc_ref(v_inst_1336_);
lean_inc_ref(v_inst_1335_);
v___x_1342_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1335_, v_inst_1336_, v_key_1340_, v_map_1339_);
if (v___x_1342_ == 0)
{
lean_dec(v_f_1341_);
lean_dec(v_key_1340_);
lean_dec_ref(v_inst_1336_);
lean_dec_ref(v_inst_1335_);
return v_map_1339_;
}
else
{
lean_object* v_entries_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_entries_1343_ = lean_ctor_get(v_map_1339_, 0);
lean_inc_ref(v_entries_1343_);
lean_dec_ref(v_map_1339_);
v___x_1344_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1335_, v_inst_1336_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_entries_1343_);
v___x_1347_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1348_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v_entries_1343_);
lean_dec(v_f_1341_);
lean_dec(v_key_1340_);
lean_dec_ref(v_inst_1336_);
lean_dec_ref(v_inst_1335_);
return v___x_1344_;
}
else
{
lean_object* v___f_1349_; uint8_t v___x_1350_; 
v___f_1349_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_update___redArg___lam__1), 6, 4);
lean_closure_set(v___f_1349_, 0, v_inst_1335_);
lean_closure_set(v___f_1349_, 1, v_inst_1336_);
lean_closure_set(v___f_1349_, 2, v_key_1340_);
lean_closure_set(v___f_1349_, 3, v_f_1341_);
v___x_1350_ = lean_nat_dec_le(v___x_1346_, v___x_1346_);
if (v___x_1350_ == 0)
{
if (v___x_1348_ == 0)
{
lean_dec_ref(v___f_1349_);
lean_dec_ref(v_entries_1343_);
return v___x_1344_;
}
else
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = lean_usize_of_nat(v___x_1346_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1347_, v___f_1349_, v_entries_1343_, v___x_1351_, v___x_1352_, v___x_1344_);
return v___x_1353_;
}
}
else
{
size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1346_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1347_, v___f_1349_, v_entries_1343_, v___x_1354_, v___x_1355_, v___x_1344_);
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast___redArg(lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_map_1359_, lean_object* v_key_1360_, lean_object* v_value_1361_){
_start:
{
uint8_t v___x_1362_; 
lean_inc(v_key_1360_);
lean_inc_ref(v_inst_1358_);
lean_inc_ref(v_inst_1357_);
v___x_1362_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1357_, v_inst_1358_, v_key_1360_, v_map_1359_);
if (v___x_1362_ == 0)
{
lean_dec(v_value_1361_);
lean_dec(v_key_1360_);
lean_dec_ref(v_inst_1358_);
lean_dec_ref(v_inst_1357_);
return v_map_1359_;
}
else
{
lean_object* v_entries_1363_; lean_object* v_indexes_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1379_; 
v_entries_1363_ = lean_ctor_get(v_map_1359_, 0);
v_indexes_1364_ = lean_ctor_get(v_map_1359_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_map_1359_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1366_ = v_map_1359_;
v_isShared_1367_ = v_isSharedCheck_1379_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_indexes_1364_);
lean_inc(v_entries_1363_);
lean_dec(v_map_1359_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1379_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v_val_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_lastIdx_1373_; lean_object* v___x_1374_; lean_object* v_entries_1375_; lean_object* v___x_1377_; 
lean_inc(v_key_1360_);
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1357_, v_inst_1358_, v_indexes_1364_, v_key_1360_);
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1369_);
lean_dec(v___x_1368_);
v___x_1370_ = lean_array_get_size(v_val_1369_);
v___x_1371_ = lean_unsigned_to_nat(1u);
v___x_1372_ = lean_nat_sub(v___x_1370_, v___x_1371_);
v_lastIdx_1373_ = lean_array_fget(v_val_1369_, v___x_1372_);
lean_dec(v___x_1372_);
lean_dec(v_val_1369_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_key_1360_);
lean_ctor_set(v___x_1374_, 1, v_value_1361_);
v_entries_1375_ = lean_array_fset(v_entries_1363_, v_lastIdx_1373_, v___x_1374_);
lean_dec(v_lastIdx_1373_);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_entries_1375_);
v___x_1377_ = v___x_1366_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_entries_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_indexes_1364_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_replaceLast(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_map_1384_, lean_object* v_key_1385_, lean_object* v_value_1386_){
_start:
{
uint8_t v___x_1387_; 
lean_inc(v_key_1385_);
lean_inc_ref(v_inst_1383_);
lean_inc_ref(v_inst_1382_);
v___x_1387_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1382_, v_inst_1383_, v_key_1385_, v_map_1384_);
if (v___x_1387_ == 0)
{
lean_dec(v_value_1386_);
lean_dec(v_key_1385_);
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
return v_map_1384_;
}
else
{
lean_object* v_entries_1388_; lean_object* v_indexes_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1404_; 
v_entries_1388_ = lean_ctor_get(v_map_1384_, 0);
v_indexes_1389_ = lean_ctor_get(v_map_1384_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_map_1384_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1391_ = v_map_1384_;
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_indexes_1389_);
lean_inc(v_entries_1388_);
lean_dec(v_map_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1404_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v_val_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_lastIdx_1398_; lean_object* v___x_1399_; lean_object* v_entries_1400_; lean_object* v___x_1402_; 
lean_inc(v_key_1385_);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1382_, v_inst_1383_, v_indexes_1389_, v_key_1385_);
v_val_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_val_1394_);
lean_dec(v___x_1393_);
v___x_1395_ = lean_array_get_size(v_val_1394_);
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_sub(v___x_1395_, v___x_1396_);
v_lastIdx_1398_ = lean_array_fget(v_val_1394_, v___x_1397_);
lean_dec(v___x_1397_);
lean_dec(v_val_1394_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_key_1385_);
lean_ctor_set(v___x_1399_, 1, v_value_1386_);
v_entries_1400_ = lean_array_fset(v_entries_1388_, v_lastIdx_1398_, v___x_1399_);
lean_dec(v_lastIdx_1398_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_entries_1400_);
v___x_1402_ = v___x_1391_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_entries_1400_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_indexes_1389_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg___lam__1(lean_object* v_inst_1405_, lean_object* v_key_1406_, lean_object* v_inst_1407_, lean_object* v_x1_1408_, lean_object* v_x2_1409_){
_start:
{
lean_object* v_fst_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_fst_1410_ = lean_ctor_get(v_x2_1409_, 0);
lean_inc_n(v_fst_1410_, 2);
lean_inc_ref(v_inst_1405_);
v___x_1411_ = lean_apply_2(v_inst_1405_, v_key_1406_, v_fst_1410_);
v___x_1412_ = lean_unbox(v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v_entries_1413_; lean_object* v_indexes_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1508_; 
v_entries_1413_ = lean_ctor_get(v_x1_1408_, 0);
v_indexes_1414_ = lean_ctor_get(v_x1_1408_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_x1_1408_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1416_ = v_x1_1408_;
v_isShared_1417_ = v_isSharedCheck_1508_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_indexes_1414_);
lean_inc(v_entries_1413_);
lean_dec(v_x1_1408_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1508_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_i_1418_; lean_object* v_entries_1419_; lean_object* v___x_1420_; 
v_i_1418_ = lean_array_get_size(v_entries_1413_);
v_entries_1419_ = lean_array_push(v_entries_1413_, v_x2_1409_);
lean_inc(v_fst_1410_);
lean_inc_ref(v_inst_1407_);
lean_inc_ref(v_inst_1405_);
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1405_, v_inst_1407_, v_indexes_1414_, v_fst_1410_);
switch(lean_obj_tag(v___x_1420_))
{
case 0:
{
lean_object* v_index_1421_; lean_object* v_value_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_val_1425_; lean_object* v_size_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1405_);
v_index_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_index_1421_);
v_value_1422_ = lean_ctor_get(v___x_1420_, 2);
lean_inc(v_value_1422_);
lean_dec_ref_known(v___x_1420_, 3);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_value_1422_);
v___x_1424_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1418_, v___x_1423_);
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec(v___x_1424_);
v_size_1426_ = lean_ctor_get(v_indexes_1414_, 0);
lean_inc(v_size_1426_);
v___x_1427_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1414_, v_size_1426_, v_index_1421_, v_fst_1410_, v_val_1425_);
lean_dec(v_index_1421_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1427_);
lean_ctor_set(v___x_1416_, 0, v_entries_1419_);
v___x_1429_ = v___x_1416_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_entries_1419_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
case 1:
{
lean_object* v_index_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_val_1434_; lean_object* v___y_1436_; lean_object* v_i_1437_; lean_object* v_size_1457_; lean_object* v_keyArray_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_index_1431_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_index_1431_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1432_ = lean_box(0);
v___x_1433_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1418_, v___x_1432_);
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec(v___x_1433_);
v_size_1457_ = lean_ctor_get(v_indexes_1414_, 0);
v_keyArray_1458_ = lean_ctor_get(v_indexes_1414_, 1);
v___x_1459_ = lean_unsigned_to_nat(1u);
v___x_1460_ = lean_nat_add(v_size_1457_, v___x_1459_);
v___x_1461_ = lean_array_get_size(v_keyArray_1458_);
v___x_1462_ = lean_nat_dec_lt(v___x_1460_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_dec(v___x_1460_);
lean_dec(v_index_1431_);
goto v___jp_1445_;
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1463_ = lean_unsigned_to_nat(4u);
v___x_1464_ = lean_nat_mul(v___x_1460_, v___x_1463_);
v___x_1465_ = lean_unsigned_to_nat(3u);
v___x_1466_ = lean_nat_mul(v___x_1461_, v___x_1465_);
v___x_1467_ = lean_nat_dec_le(v___x_1464_, v___x_1466_);
lean_dec(v___x_1466_);
lean_dec(v___x_1464_);
if (v___x_1467_ == 0)
{
lean_dec(v___x_1460_);
lean_dec(v_index_1431_);
goto v___jp_1445_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1416_);
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1405_);
v___x_1468_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1414_, v___x_1460_, v_index_1431_, v_fst_1410_, v_val_1434_);
lean_dec(v_index_1431_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_entries_1419_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
return v___x_1469_;
}
}
v___jp_1435_:
{
lean_object* v_size_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v_size_1438_ = lean_ctor_get(v___y_1436_, 0);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = lean_nat_add(v_size_1438_, v___x_1439_);
v___x_1441_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1436_, v___x_1440_, v_i_1437_, v_fst_1410_, v_val_1434_);
lean_dec(v_i_1437_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1441_);
lean_ctor_set(v___x_1416_, 0, v_entries_1419_);
v___x_1443_ = v___x_1416_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_entries_1419_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
v___jp_1445_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
lean_inc_ref(v_inst_1407_);
lean_inc_ref(v_inst_1405_);
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1405_, v_inst_1407_, v_indexes_1414_);
lean_inc(v_fst_1410_);
v___x_1447_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1405_, v_inst_1407_, v___x_1446_, v_fst_1410_);
switch(lean_obj_tag(v___x_1447_))
{
case 0:
{
lean_object* v_index_1448_; lean_object* v_size_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_del_object(v___x_1416_);
v_index_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_index_1448_);
lean_dec_ref_known(v___x_1447_, 3);
v_size_1449_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_size_1449_);
v___x_1450_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1446_, v_size_1449_, v_index_1448_, v_fst_1410_, v_val_1434_);
lean_dec(v_index_1448_);
v___x_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_entries_1419_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
return v___x_1451_;
}
case 1:
{
lean_object* v_index_1452_; 
v_index_1452_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_index_1452_);
lean_dec_ref_known(v___x_1447_, 1);
v___y_1436_ = v___x_1446_;
v_i_1437_ = v_index_1452_;
goto v___jp_1435_;
}
default: 
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1446_, v___x_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_index_1455_; 
v_index_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_index_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v___y_1436_ = v___x_1446_;
v_i_1437_ = v_index_1455_;
goto v___jp_1435_;
}
else
{
lean_object* v___x_1456_; 
lean_dec(v_val_1434_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1410_);
v___x_1456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_entries_1419_);
lean_ctor_set(v___x_1456_, 1, v___x_1446_);
return v___x_1456_;
}
}
}
}
}
default: 
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_val_1472_; lean_object* v___y_1474_; lean_object* v_i_1475_; lean_object* v___y_1484_; lean_object* v_size_1495_; lean_object* v_keyArray_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1470_ = lean_box(0);
v___x_1471_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1418_, v___x_1470_);
v_val_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_val_1472_);
lean_dec(v___x_1471_);
v_size_1495_ = lean_ctor_get(v_indexes_1414_, 0);
v_keyArray_1496_ = lean_ctor_get(v_indexes_1414_, 1);
v___x_1497_ = lean_unsigned_to_nat(1u);
v___x_1498_ = lean_nat_add(v_size_1495_, v___x_1497_);
v___x_1499_ = lean_array_get_size(v_keyArray_1496_);
v___x_1500_ = lean_nat_dec_lt(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; 
lean_dec(v___x_1498_);
lean_inc_ref(v_inst_1407_);
lean_inc_ref(v_inst_1405_);
v___x_1501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1405_, v_inst_1407_, v_indexes_1414_);
v___y_1484_ = v___x_1501_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1502_ = lean_unsigned_to_nat(4u);
v___x_1503_ = lean_nat_mul(v___x_1498_, v___x_1502_);
lean_dec(v___x_1498_);
v___x_1504_ = lean_unsigned_to_nat(3u);
v___x_1505_ = lean_nat_mul(v___x_1499_, v___x_1504_);
v___x_1506_ = lean_nat_dec_le(v___x_1503_, v___x_1505_);
lean_dec(v___x_1505_);
lean_dec(v___x_1503_);
if (v___x_1506_ == 0)
{
lean_object* v___x_1507_; 
lean_inc_ref(v_inst_1407_);
lean_inc_ref(v_inst_1405_);
v___x_1507_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1405_, v_inst_1407_, v_indexes_1414_);
v___y_1484_ = v___x_1507_;
goto v___jp_1483_;
}
else
{
v___y_1484_ = v_indexes_1414_;
goto v___jp_1483_;
}
}
v___jp_1473_:
{
lean_object* v_size_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v_size_1476_ = lean_ctor_get(v___y_1474_, 0);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_size_1476_, v___x_1477_);
v___x_1479_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1474_, v___x_1478_, v_i_1475_, v_fst_1410_, v_val_1472_);
lean_dec(v_i_1475_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v___x_1479_);
lean_ctor_set(v___x_1416_, 0, v_entries_1419_);
v___x_1481_ = v___x_1416_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_entries_1419_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
v___jp_1483_:
{
lean_object* v___x_1485_; 
lean_inc(v_fst_1410_);
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1405_, v_inst_1407_, v___y_1484_, v_fst_1410_);
switch(lean_obj_tag(v___x_1485_))
{
case 0:
{
lean_object* v_index_1486_; lean_object* v_size_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_del_object(v___x_1416_);
v_index_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_index_1486_);
lean_dec_ref_known(v___x_1485_, 3);
v_size_1487_ = lean_ctor_get(v___y_1484_, 0);
lean_inc(v_size_1487_);
v___x_1488_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1484_, v_size_1487_, v_index_1486_, v_fst_1410_, v_val_1472_);
lean_dec(v_index_1486_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_entries_1419_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
return v___x_1489_;
}
case 1:
{
lean_object* v_index_1490_; 
v_index_1490_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_index_1490_);
lean_dec_ref_known(v___x_1485_, 1);
v___y_1474_ = v___y_1484_;
v_i_1475_ = v_index_1490_;
goto v___jp_1473_;
}
default: 
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1484_, v___x_1491_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_index_1493_; 
v_index_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_index_1493_);
lean_dec_ref_known(v___x_1492_, 1);
v___y_1474_ = v___y_1484_;
v_i_1475_ = v_index_1493_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1494_; 
lean_dec(v_val_1472_);
lean_del_object(v___x_1416_);
lean_dec(v_fst_1410_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_entries_1419_);
lean_ctor_set(v___x_1494_, 1, v___y_1484_);
return v___x_1494_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1410_);
lean_dec_ref(v_x2_1409_);
lean_dec_ref(v_inst_1407_);
lean_dec_ref(v_inst_1405_);
return v_x1_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase___redArg(lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_map_1511_, lean_object* v_key_1512_){
_start:
{
uint8_t v___x_1513_; 
lean_inc(v_key_1512_);
lean_inc_ref(v_inst_1510_);
lean_inc_ref(v_inst_1509_);
v___x_1513_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1509_, v_inst_1510_, v_key_1512_, v_map_1511_);
if (v___x_1513_ == 0)
{
lean_dec(v_key_1512_);
lean_dec_ref(v_inst_1510_);
lean_dec_ref(v_inst_1509_);
return v_map_1511_;
}
else
{
lean_object* v_entries_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_entries_1514_ = lean_ctor_get(v_map_1511_, 0);
lean_inc_ref(v_entries_1514_);
lean_dec_ref(v_map_1511_);
v___x_1515_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1509_, v_inst_1510_);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_entries_1514_);
v___x_1518_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1519_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v_entries_1514_);
lean_dec(v_key_1512_);
lean_dec_ref(v_inst_1510_);
lean_dec_ref(v_inst_1509_);
return v___x_1515_;
}
else
{
lean_object* v___f_1520_; uint8_t v___x_1521_; 
v___f_1520_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1520_, 0, v_inst_1509_);
lean_closure_set(v___f_1520_, 1, v_key_1512_);
lean_closure_set(v___f_1520_, 2, v_inst_1510_);
v___x_1521_ = lean_nat_dec_le(v___x_1517_, v___x_1517_);
if (v___x_1521_ == 0)
{
if (v___x_1519_ == 0)
{
lean_dec_ref(v___f_1520_);
lean_dec_ref(v_entries_1514_);
return v___x_1515_;
}
else
{
size_t v___x_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = lean_usize_of_nat(v___x_1517_);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1518_, v___f_1520_, v_entries_1514_, v___x_1522_, v___x_1523_, v___x_1515_);
return v___x_1524_;
}
}
else
{
size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1517_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1518_, v___f_1520_, v_entries_1514_, v___x_1525_, v___x_1526_, v___x_1515_);
return v___x_1527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_erase(lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_inst_1530_, lean_object* v_inst_1531_, lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_map_1534_, lean_object* v_key_1535_){
_start:
{
uint8_t v___x_1536_; 
lean_inc(v_key_1535_);
lean_inc_ref(v_inst_1531_);
lean_inc_ref(v_inst_1530_);
v___x_1536_ = l_Std_Internal_IndexMultiMap_instDecidableMem___redArg(v_inst_1530_, v_inst_1531_, v_key_1535_, v_map_1534_);
if (v___x_1536_ == 0)
{
lean_dec(v_key_1535_);
lean_dec_ref(v_inst_1531_);
lean_dec_ref(v_inst_1530_);
return v_map_1534_;
}
else
{
lean_object* v_entries_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_entries_1537_ = lean_ctor_get(v_map_1534_, 0);
lean_inc_ref(v_entries_1537_);
lean_dec_ref(v_map_1534_);
v___x_1538_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1530_, v_inst_1531_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = lean_array_get_size(v_entries_1537_);
v___x_1541_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1542_ = lean_nat_dec_lt(v___x_1539_, v___x_1540_);
if (v___x_1542_ == 0)
{
lean_dec_ref(v_entries_1537_);
lean_dec(v_key_1535_);
lean_dec_ref(v_inst_1531_);
lean_dec_ref(v_inst_1530_);
return v___x_1538_;
}
else
{
lean_object* v___f_1543_; uint8_t v___x_1544_; 
v___f_1543_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_erase___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1543_, 0, v_inst_1530_);
lean_closure_set(v___f_1543_, 1, v_key_1535_);
lean_closure_set(v___f_1543_, 2, v_inst_1531_);
v___x_1544_ = lean_nat_dec_le(v___x_1540_, v___x_1540_);
if (v___x_1544_ == 0)
{
if (v___x_1542_ == 0)
{
lean_dec_ref(v___f_1543_);
lean_dec_ref(v_entries_1537_);
return v___x_1538_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = lean_usize_of_nat(v___x_1540_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1541_, v___f_1543_, v_entries_1537_, v___x_1545_, v___x_1546_, v___x_1538_);
return v___x_1547_;
}
}
else
{
size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1540_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1541_, v___f_1543_, v_entries_1537_, v___x_1548_, v___x_1549_, v___x_1538_);
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1(lean_object* v_inst_1551_, lean_object* v_keys_1552_, lean_object* v_inst_1553_, lean_object* v_x1_1554_, lean_object* v_x2_1555_){
_start:
{
lean_object* v_fst_1556_; uint8_t v___x_1557_; 
v_fst_1556_ = lean_ctor_get(v_x2_1555_, 0);
lean_inc_n(v_fst_1556_, 2);
lean_inc_ref(v_inst_1551_);
v___x_1557_ = l_Array_contains___redArg(v_inst_1551_, v_keys_1552_, v_fst_1556_);
if (v___x_1557_ == 0)
{
lean_object* v_entries_1558_; lean_object* v_indexes_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1653_; 
v_entries_1558_ = lean_ctor_get(v_x1_1554_, 0);
v_indexes_1559_ = lean_ctor_get(v_x1_1554_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_x1_1554_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1561_ = v_x1_1554_;
v_isShared_1562_ = v_isSharedCheck_1653_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_indexes_1559_);
lean_inc(v_entries_1558_);
lean_dec(v_x1_1554_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1653_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_i_1563_; lean_object* v_entries_1564_; lean_object* v___x_1565_; 
v_i_1563_ = lean_array_get_size(v_entries_1558_);
v_entries_1564_ = lean_array_push(v_entries_1558_, v_x2_1555_);
lean_inc(v_fst_1556_);
lean_inc_ref(v_inst_1553_);
lean_inc_ref(v_inst_1551_);
v___x_1565_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1551_, v_inst_1553_, v_indexes_1559_, v_fst_1556_);
switch(lean_obj_tag(v___x_1565_))
{
case 0:
{
lean_object* v_index_1566_; lean_object* v_value_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v_val_1570_; lean_object* v_size_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
lean_dec_ref(v_inst_1553_);
lean_dec_ref(v_inst_1551_);
v_index_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_index_1566_);
v_value_1567_ = lean_ctor_get(v___x_1565_, 2);
lean_inc(v_value_1567_);
lean_dec_ref_known(v___x_1565_, 3);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_value_1567_);
v___x_1569_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1563_, v___x_1568_);
v_val_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_val_1570_);
lean_dec(v___x_1569_);
v_size_1571_ = lean_ctor_get(v_indexes_1559_, 0);
lean_inc(v_size_1571_);
v___x_1572_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1559_, v_size_1571_, v_index_1566_, v_fst_1556_, v_val_1570_);
lean_dec(v_index_1566_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___x_1572_);
lean_ctor_set(v___x_1561_, 0, v_entries_1564_);
v___x_1574_ = v___x_1561_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_entries_1564_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
case 1:
{
lean_object* v_index_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_val_1579_; lean_object* v___y_1581_; lean_object* v_i_1582_; lean_object* v_size_1602_; lean_object* v_keyArray_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_index_1576_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_index_1576_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1577_ = lean_box(0);
v___x_1578_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1563_, v___x_1577_);
v_val_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_val_1579_);
lean_dec(v___x_1578_);
v_size_1602_ = lean_ctor_get(v_indexes_1559_, 0);
v_keyArray_1603_ = lean_ctor_get(v_indexes_1559_, 1);
v___x_1604_ = lean_unsigned_to_nat(1u);
v___x_1605_ = lean_nat_add(v_size_1602_, v___x_1604_);
v___x_1606_ = lean_array_get_size(v_keyArray_1603_);
v___x_1607_ = lean_nat_dec_lt(v___x_1605_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1576_);
goto v___jp_1590_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1608_ = lean_unsigned_to_nat(4u);
v___x_1609_ = lean_nat_mul(v___x_1605_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(3u);
v___x_1611_ = lean_nat_mul(v___x_1606_, v___x_1610_);
v___x_1612_ = lean_nat_dec_le(v___x_1609_, v___x_1611_);
lean_dec(v___x_1611_);
lean_dec(v___x_1609_);
if (v___x_1612_ == 0)
{
lean_dec(v___x_1605_);
lean_dec(v_index_1576_);
goto v___jp_1590_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_del_object(v___x_1561_);
lean_dec_ref(v_inst_1553_);
lean_dec_ref(v_inst_1551_);
v___x_1613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1559_, v___x_1605_, v_index_1576_, v_fst_1556_, v_val_1579_);
lean_dec(v_index_1576_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_entries_1564_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
return v___x_1614_;
}
}
v___jp_1580_:
{
lean_object* v_size_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_size_1583_ = lean_ctor_get(v___y_1581_, 0);
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_nat_add(v_size_1583_, v___x_1584_);
v___x_1586_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1581_, v___x_1585_, v_i_1582_, v_fst_1556_, v_val_1579_);
lean_dec(v_i_1582_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___x_1586_);
lean_ctor_set(v___x_1561_, 0, v_entries_1564_);
v___x_1588_ = v___x_1561_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_entries_1564_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
v___jp_1590_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_inc_ref(v_inst_1553_);
lean_inc_ref(v_inst_1551_);
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1551_, v_inst_1553_, v_indexes_1559_);
lean_inc(v_fst_1556_);
v___x_1592_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1551_, v_inst_1553_, v___x_1591_, v_fst_1556_);
switch(lean_obj_tag(v___x_1592_))
{
case 0:
{
lean_object* v_index_1593_; lean_object* v_size_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_del_object(v___x_1561_);
v_index_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_index_1593_);
lean_dec_ref_known(v___x_1592_, 3);
v_size_1594_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_size_1594_);
v___x_1595_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1591_, v_size_1594_, v_index_1593_, v_fst_1556_, v_val_1579_);
lean_dec(v_index_1593_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_entries_1564_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
return v___x_1596_;
}
case 1:
{
lean_object* v_index_1597_; 
v_index_1597_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_index_1597_);
lean_dec_ref_known(v___x_1592_, 1);
v___y_1581_ = v___x_1591_;
v_i_1582_ = v_index_1597_;
goto v___jp_1580_;
}
default: 
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1591_, v___x_1598_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_index_1600_; 
v_index_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_index_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___y_1581_ = v___x_1591_;
v_i_1582_ = v_index_1600_;
goto v___jp_1580_;
}
else
{
lean_object* v___x_1601_; 
lean_dec(v_val_1579_);
lean_del_object(v___x_1561_);
lean_dec(v_fst_1556_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_entries_1564_);
lean_ctor_set(v___x_1601_, 1, v___x_1591_);
return v___x_1601_;
}
}
}
}
}
default: 
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_val_1617_; lean_object* v___y_1619_; lean_object* v_i_1620_; lean_object* v___y_1629_; lean_object* v_size_1640_; lean_object* v_keyArray_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1615_ = lean_box(0);
v___x_1616_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1563_, v___x_1615_);
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_val_1617_);
lean_dec(v___x_1616_);
v_size_1640_ = lean_ctor_get(v_indexes_1559_, 0);
v_keyArray_1641_ = lean_ctor_get(v_indexes_1559_, 1);
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_add(v_size_1640_, v___x_1642_);
v___x_1644_ = lean_array_get_size(v_keyArray_1641_);
v___x_1645_ = lean_nat_dec_lt(v___x_1643_, v___x_1644_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec(v___x_1643_);
lean_inc_ref(v_inst_1553_);
lean_inc_ref(v_inst_1551_);
v___x_1646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1551_, v_inst_1553_, v_indexes_1559_);
v___y_1629_ = v___x_1646_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v___x_1647_ = lean_unsigned_to_nat(4u);
v___x_1648_ = lean_nat_mul(v___x_1643_, v___x_1647_);
lean_dec(v___x_1643_);
v___x_1649_ = lean_unsigned_to_nat(3u);
v___x_1650_ = lean_nat_mul(v___x_1644_, v___x_1649_);
v___x_1651_ = lean_nat_dec_le(v___x_1648_, v___x_1650_);
lean_dec(v___x_1650_);
lean_dec(v___x_1648_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_inc_ref(v_inst_1553_);
lean_inc_ref(v_inst_1551_);
v___x_1652_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1551_, v_inst_1553_, v_indexes_1559_);
v___y_1629_ = v___x_1652_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v_indexes_1559_;
goto v___jp_1628_;
}
}
v___jp_1618_:
{
lean_object* v_size_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v_size_1621_ = lean_ctor_get(v___y_1619_, 0);
v___x_1622_ = lean_unsigned_to_nat(1u);
v___x_1623_ = lean_nat_add(v_size_1621_, v___x_1622_);
v___x_1624_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1619_, v___x_1623_, v_i_1620_, v_fst_1556_, v_val_1617_);
lean_dec(v_i_1620_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 1, v___x_1624_);
lean_ctor_set(v___x_1561_, 0, v_entries_1564_);
v___x_1626_ = v___x_1561_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_entries_1564_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
v___jp_1628_:
{
lean_object* v___x_1630_; 
lean_inc(v_fst_1556_);
v___x_1630_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1551_, v_inst_1553_, v___y_1629_, v_fst_1556_);
switch(lean_obj_tag(v___x_1630_))
{
case 0:
{
lean_object* v_index_1631_; lean_object* v_size_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_del_object(v___x_1561_);
v_index_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_index_1631_);
lean_dec_ref_known(v___x_1630_, 3);
v_size_1632_ = lean_ctor_get(v___y_1629_, 0);
lean_inc(v_size_1632_);
v___x_1633_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1629_, v_size_1632_, v_index_1631_, v_fst_1556_, v_val_1617_);
lean_dec(v_index_1631_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_entries_1564_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
return v___x_1634_;
}
case 1:
{
lean_object* v_index_1635_; 
v_index_1635_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_index_1635_);
lean_dec_ref_known(v___x_1630_, 1);
v___y_1619_ = v___y_1629_;
v_i_1620_ = v_index_1635_;
goto v___jp_1618_;
}
default: 
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1629_, v___x_1636_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_index_1638_; 
v_index_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_index_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___y_1619_ = v___y_1629_;
v_i_1620_ = v_index_1638_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1639_; 
lean_dec(v_val_1617_);
lean_del_object(v___x_1561_);
lean_dec(v_fst_1556_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_entries_1564_);
lean_ctor_set(v___x_1639_, 1, v___y_1629_);
return v___x_1639_;
}
}
}
}
}
}
}
}
else
{
lean_dec(v_fst_1556_);
lean_dec_ref(v_x2_1555_);
lean_dec_ref(v_inst_1553_);
lean_dec_ref(v_inst_1551_);
return v_x1_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany___redArg(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_map_1656_, lean_object* v_keys_1657_){
_start:
{
lean_object* v_entries_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_entries_1658_ = lean_ctor_get(v_map_1656_, 0);
lean_inc_ref(v_entries_1658_);
lean_dec_ref(v_map_1656_);
v___x_1659_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1654_, v_inst_1655_);
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_array_get_size(v_entries_1658_);
v___x_1662_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1663_ = lean_nat_dec_lt(v___x_1660_, v___x_1661_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_entries_1658_);
lean_dec_ref(v_keys_1657_);
lean_dec_ref(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
return v___x_1659_;
}
else
{
lean_object* v___f_1664_; uint8_t v___x_1665_; 
v___f_1664_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1664_, 0, v_inst_1654_);
lean_closure_set(v___f_1664_, 1, v_keys_1657_);
lean_closure_set(v___f_1664_, 2, v_inst_1655_);
v___x_1665_ = lean_nat_dec_le(v___x_1661_, v___x_1661_);
if (v___x_1665_ == 0)
{
if (v___x_1663_ == 0)
{
lean_dec_ref(v___f_1664_);
lean_dec_ref(v_entries_1658_);
return v___x_1659_;
}
else
{
size_t v___x_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = lean_usize_of_nat(v___x_1661_);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v___f_1664_, v_entries_1658_, v___x_1666_, v___x_1667_, v___x_1659_);
return v___x_1668_;
}
}
else
{
size_t v___x_1669_; size_t v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = ((size_t)0ULL);
v___x_1670_ = lean_usize_of_nat(v___x_1661_);
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v___f_1664_, v_entries_1658_, v___x_1669_, v___x_1670_, v___x_1659_);
return v___x_1671_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_eraseMany(lean_object* v_00_u03b1_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_map_1678_, lean_object* v_keys_1679_){
_start:
{
lean_object* v_entries_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_entries_1680_ = lean_ctor_get(v_map_1678_, 0);
lean_inc_ref(v_entries_1680_);
lean_dec_ref(v_map_1678_);
v___x_1681_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1674_, v_inst_1675_);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_array_get_size(v_entries_1680_);
v___x_1684_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1685_ = lean_nat_dec_lt(v___x_1682_, v___x_1683_);
if (v___x_1685_ == 0)
{
lean_dec_ref(v_entries_1680_);
lean_dec_ref(v_keys_1679_);
lean_dec_ref(v_inst_1675_);
lean_dec_ref(v_inst_1674_);
return v___x_1681_;
}
else
{
lean_object* v___f_1686_; uint8_t v___x_1687_; 
v___f_1686_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_eraseMany___redArg___lam__1), 5, 3);
lean_closure_set(v___f_1686_, 0, v_inst_1674_);
lean_closure_set(v___f_1686_, 1, v_keys_1679_);
lean_closure_set(v___f_1686_, 2, v_inst_1675_);
v___x_1687_ = lean_nat_dec_le(v___x_1683_, v___x_1683_);
if (v___x_1687_ == 0)
{
if (v___x_1685_ == 0)
{
lean_dec_ref(v___f_1686_);
lean_dec_ref(v_entries_1680_);
return v___x_1681_;
}
else
{
size_t v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((size_t)0ULL);
v___x_1689_ = lean_usize_of_nat(v___x_1683_);
v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1684_, v___f_1686_, v_entries_1680_, v___x_1688_, v___x_1689_, v___x_1681_);
return v___x_1690_;
}
}
else
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = lean_usize_of_nat(v___x_1683_);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1684_, v___f_1686_, v_entries_1680_, v___x_1691_, v___x_1692_, v___x_1681_);
return v___x_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg(lean_object* v_map_1694_){
_start:
{
lean_object* v_entries_1695_; lean_object* v___x_1696_; 
v_entries_1695_ = lean_ctor_get(v_map_1694_, 0);
v___x_1696_ = lean_array_get_size(v_entries_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___redArg___boxed(lean_object* v_map_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_Internal_IndexMultiMap_size___redArg(v_map_1697_);
lean_dec_ref(v_map_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_map_1703_){
_start:
{
lean_object* v_entries_1704_; lean_object* v___x_1705_; 
v_entries_1704_ = lean_ctor_get(v_map_1703_, 0);
v___x_1705_ = lean_array_get_size(v_entries_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_size___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_map_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_Internal_IndexMultiMap_size(v_00_u03b1_1706_, v_00_u03b2_1707_, v_inst_1708_, v_inst_1709_, v_map_1710_);
lean_dec_ref(v_map_1710_);
lean_dec_ref(v_inst_1709_);
lean_dec_ref(v_inst_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty___redArg(lean_object* v_map_1712_){
_start:
{
lean_object* v_entries_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_entries_1713_ = lean_ctor_get(v_map_1712_, 0);
v___x_1714_ = lean_array_get_size(v_entries_1713_);
v___x_1715_ = lean_unsigned_to_nat(0u);
v___x_1716_ = lean_nat_dec_eq(v___x_1714_, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___redArg___boxed(lean_object* v_map_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Std_Internal_IndexMultiMap_isEmpty___redArg(v_map_1717_);
lean_dec_ref(v_map_1717_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_IndexMultiMap_isEmpty(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_map_1724_){
_start:
{
lean_object* v_entries_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_entries_1725_ = lean_ctor_get(v_map_1724_, 0);
v___x_1726_ = lean_array_get_size(v_entries_1725_);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_nat_dec_eq(v___x_1726_, v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_isEmpty___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_map_1733_){
_start:
{
uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_res_1734_ = l_Std_Internal_IndexMultiMap_isEmpty(v_00_u03b1_1729_, v_00_u03b2_1730_, v_inst_1731_, v_inst_1732_, v_map_1733_);
lean_dec_ref(v_map_1733_);
lean_dec_ref(v_inst_1732_);
lean_dec_ref(v_inst_1731_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg(lean_object* v_map_1736_){
_start:
{
lean_object* v_entries_1737_; 
v_entries_1737_ = lean_ctor_get(v_map_1736_, 0);
lean_inc_ref(v_entries_1737_);
return v_entries_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___redArg___boxed(lean_object* v_map_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Std_Internal_IndexMultiMap_toArray___redArg(v_map_1738_);
lean_dec_ref(v_map_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_map_1744_){
_start:
{
lean_object* v_entries_1745_; 
v_entries_1745_ = lean_ctor_get(v_map_1744_, 0);
lean_inc_ref(v_entries_1745_);
return v_entries_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toArray___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_map_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_Internal_IndexMultiMap_toArray(v_00_u03b1_1746_, v_00_u03b2_1747_, v_inst_1748_, v_inst_1749_, v_map_1750_);
lean_dec_ref(v_map_1750_);
lean_dec_ref(v_inst_1749_);
lean_dec_ref(v_inst_1748_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___redArg(lean_object* v_map_1752_){
_start:
{
lean_object* v_entries_1753_; lean_object* v___x_1754_; 
v_entries_1753_ = lean_ctor_get(v_map_1752_, 0);
lean_inc_ref(v_entries_1753_);
lean_dec_ref(v_map_1752_);
v___x_1754_ = lean_array_to_list(v_entries_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_map_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_Internal_IndexMultiMap_toList___redArg(v_map_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_toList___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_map_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_Internal_IndexMultiMap_toList(v_00_u03b1_1761_, v_00_u03b2_1762_, v_inst_1763_, v_inst_1764_, v_map_1765_);
lean_dec_ref(v_inst_1764_);
lean_dec_ref(v_inst_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg___lam__1(lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_x1_1769_, lean_object* v_x2_1770_){
_start:
{
lean_object* v_fst_1771_; lean_object* v_entries_1772_; lean_object* v_indexes_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1867_; 
v_fst_1771_ = lean_ctor_get(v_x2_1770_, 0);
lean_inc(v_fst_1771_);
v_entries_1772_ = lean_ctor_get(v_x1_1769_, 0);
v_indexes_1773_ = lean_ctor_get(v_x1_1769_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_x1_1769_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1775_ = v_x1_1769_;
v_isShared_1776_ = v_isSharedCheck_1867_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_indexes_1773_);
lean_inc(v_entries_1772_);
lean_dec(v_x1_1769_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1867_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_i_1777_; lean_object* v_entries_1778_; lean_object* v___x_1779_; 
v_i_1777_ = lean_array_get_size(v_entries_1772_);
v_entries_1778_ = lean_array_push(v_entries_1772_, v_x2_1770_);
lean_inc(v_fst_1771_);
lean_inc_ref(v_inst_1768_);
lean_inc_ref(v_inst_1767_);
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1767_, v_inst_1768_, v_indexes_1773_, v_fst_1771_);
switch(lean_obj_tag(v___x_1779_))
{
case 0:
{
lean_object* v_index_1780_; lean_object* v_value_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_val_1784_; lean_object* v_size_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
v_index_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_index_1780_);
v_value_1781_ = lean_ctor_get(v___x_1779_, 2);
lean_inc(v_value_1781_);
lean_dec_ref_known(v___x_1779_, 3);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_value_1781_);
v___x_1783_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1777_, v___x_1782_);
v_val_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_val_1784_);
lean_dec(v___x_1783_);
v_size_1785_ = lean_ctor_get(v_indexes_1773_, 0);
lean_inc(v_size_1785_);
v___x_1786_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1773_, v_size_1785_, v_index_1780_, v_fst_1771_, v_val_1784_);
lean_dec(v_index_1780_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1786_);
lean_ctor_set(v___x_1775_, 0, v_entries_1778_);
v___x_1788_ = v___x_1775_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_entries_1778_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
case 1:
{
lean_object* v_index_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v_val_1793_; lean_object* v___y_1795_; lean_object* v_i_1796_; lean_object* v_size_1816_; lean_object* v_keyArray_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_index_1790_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_index_1790_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1791_ = lean_box(0);
v___x_1792_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1777_, v___x_1791_);
v_val_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_val_1793_);
lean_dec(v___x_1792_);
v_size_1816_ = lean_ctor_get(v_indexes_1773_, 0);
v_keyArray_1817_ = lean_ctor_get(v_indexes_1773_, 1);
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = lean_nat_add(v_size_1816_, v___x_1818_);
v___x_1820_ = lean_array_get_size(v_keyArray_1817_);
v___x_1821_ = lean_nat_dec_lt(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1819_);
lean_dec(v_index_1790_);
goto v___jp_1804_;
}
else
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1822_ = lean_unsigned_to_nat(4u);
v___x_1823_ = lean_nat_mul(v___x_1819_, v___x_1822_);
v___x_1824_ = lean_unsigned_to_nat(3u);
v___x_1825_ = lean_nat_mul(v___x_1820_, v___x_1824_);
v___x_1826_ = lean_nat_dec_le(v___x_1823_, v___x_1825_);
lean_dec(v___x_1825_);
lean_dec(v___x_1823_);
if (v___x_1826_ == 0)
{
lean_dec(v___x_1819_);
lean_dec(v_index_1790_);
goto v___jp_1804_;
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_del_object(v___x_1775_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
v___x_1827_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1773_, v___x_1819_, v_index_1790_, v_fst_1771_, v_val_1793_);
lean_dec(v_index_1790_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_entries_1778_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
return v___x_1828_;
}
}
v___jp_1794_:
{
lean_object* v_size_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v_size_1797_ = lean_ctor_get(v___y_1795_, 0);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_size_1797_, v___x_1798_);
v___x_1800_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1795_, v___x_1799_, v_i_1796_, v_fst_1771_, v_val_1793_);
lean_dec(v_i_1796_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1800_);
lean_ctor_set(v___x_1775_, 0, v_entries_1778_);
v___x_1802_ = v___x_1775_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_entries_1778_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
v___jp_1804_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_inc_ref(v_inst_1768_);
lean_inc_ref(v_inst_1767_);
v___x_1805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1767_, v_inst_1768_, v_indexes_1773_);
lean_inc(v_fst_1771_);
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1767_, v_inst_1768_, v___x_1805_, v_fst_1771_);
switch(lean_obj_tag(v___x_1806_))
{
case 0:
{
lean_object* v_index_1807_; lean_object* v_size_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_del_object(v___x_1775_);
v_index_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_index_1807_);
lean_dec_ref_known(v___x_1806_, 3);
v_size_1808_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_size_1808_);
v___x_1809_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1805_, v_size_1808_, v_index_1807_, v_fst_1771_, v_val_1793_);
lean_dec(v_index_1807_);
v___x_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1810_, 0, v_entries_1778_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
return v___x_1810_;
}
case 1:
{
lean_object* v_index_1811_; 
v_index_1811_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_index_1811_);
lean_dec_ref_known(v___x_1806_, 1);
v___y_1795_ = v___x_1805_;
v_i_1796_ = v_index_1811_;
goto v___jp_1794_;
}
default: 
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1805_, v___x_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_index_1814_; 
v_index_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_index_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v___y_1795_ = v___x_1805_;
v_i_1796_ = v_index_1814_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1815_; 
lean_dec(v_val_1793_);
lean_del_object(v___x_1775_);
lean_dec(v_fst_1771_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_entries_1778_);
lean_ctor_set(v___x_1815_, 1, v___x_1805_);
return v___x_1815_;
}
}
}
}
}
default: 
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v_val_1831_; lean_object* v___y_1833_; lean_object* v_i_1834_; lean_object* v___y_1843_; lean_object* v_size_1854_; lean_object* v_keyArray_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1829_ = lean_box(0);
v___x_1830_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1777_, v___x_1829_);
v_val_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_val_1831_);
lean_dec(v___x_1830_);
v_size_1854_ = lean_ctor_get(v_indexes_1773_, 0);
v_keyArray_1855_ = lean_ctor_get(v_indexes_1773_, 1);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_size_1854_, v___x_1856_);
v___x_1858_ = lean_array_get_size(v_keyArray_1855_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec(v___x_1857_);
lean_inc_ref(v_inst_1768_);
lean_inc_ref(v_inst_1767_);
v___x_1860_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1767_, v_inst_1768_, v_indexes_1773_);
v___y_1843_ = v___x_1860_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1861_ = lean_unsigned_to_nat(4u);
v___x_1862_ = lean_nat_mul(v___x_1857_, v___x_1861_);
lean_dec(v___x_1857_);
v___x_1863_ = lean_unsigned_to_nat(3u);
v___x_1864_ = lean_nat_mul(v___x_1858_, v___x_1863_);
v___x_1865_ = lean_nat_dec_le(v___x_1862_, v___x_1864_);
lean_dec(v___x_1864_);
lean_dec(v___x_1862_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_inc_ref(v_inst_1768_);
lean_inc_ref(v_inst_1767_);
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1767_, v_inst_1768_, v_indexes_1773_);
v___y_1843_ = v___x_1866_;
goto v___jp_1842_;
}
else
{
v___y_1843_ = v_indexes_1773_;
goto v___jp_1842_;
}
}
v___jp_1832_:
{
lean_object* v_size_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_size_1835_ = lean_ctor_get(v___y_1833_, 0);
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_nat_add(v_size_1835_, v___x_1836_);
v___x_1838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1833_, v___x_1837_, v_i_1834_, v_fst_1771_, v_val_1831_);
lean_dec(v_i_1834_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1838_);
lean_ctor_set(v___x_1775_, 0, v_entries_1778_);
v___x_1840_ = v___x_1775_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_entries_1778_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; 
lean_inc(v_fst_1771_);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1767_, v_inst_1768_, v___y_1843_, v_fst_1771_);
switch(lean_obj_tag(v___x_1844_))
{
case 0:
{
lean_object* v_index_1845_; lean_object* v_size_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_del_object(v___x_1775_);
v_index_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_index_1845_);
lean_dec_ref_known(v___x_1844_, 3);
v_size_1846_ = lean_ctor_get(v___y_1843_, 0);
lean_inc(v_size_1846_);
v___x_1847_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1843_, v_size_1846_, v_index_1845_, v_fst_1771_, v_val_1831_);
lean_dec(v_index_1845_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_entries_1778_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
return v___x_1848_;
}
case 1:
{
lean_object* v_index_1849_; 
v_index_1849_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_index_1849_);
lean_dec_ref_known(v___x_1844_, 1);
v___y_1833_ = v___y_1843_;
v_i_1834_ = v_index_1849_;
goto v___jp_1832_;
}
default: 
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1843_, v___x_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_index_1852_; 
v_index_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_index_1852_);
lean_dec_ref_known(v___x_1851_, 1);
v___y_1833_ = v___y_1843_;
v_i_1834_ = v_index_1852_;
goto v___jp_1832_;
}
else
{
lean_object* v___x_1853_; 
lean_dec(v_val_1831_);
lean_del_object(v___x_1775_);
lean_dec(v_fst_1771_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_entries_1778_);
lean_ctor_set(v___x_1853_, 1, v___y_1843_);
return v___x_1853_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge___redArg(lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_m1_1870_, lean_object* v_m2_1871_){
_start:
{
lean_object* v_entries_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; 
v_entries_1872_ = lean_ctor_get(v_m2_1871_, 0);
lean_inc_ref(v_entries_1872_);
lean_dec_ref(v_m2_1871_);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_array_get_size(v_entries_1872_);
v___x_1875_ = ((lean_object*)(l_Std_Internal_instReprIndexMultiMap_repr___redArg___closed__27));
v___x_1876_ = lean_nat_dec_lt(v___x_1873_, v___x_1874_);
if (v___x_1876_ == 0)
{
lean_dec_ref(v_entries_1872_);
lean_dec_ref(v_inst_1869_);
lean_dec_ref(v_inst_1868_);
return v_m1_1870_;
}
else
{
lean_object* v___f_1877_; uint8_t v___x_1878_; 
v___f_1877_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1877_, 0, v_inst_1868_);
lean_closure_set(v___f_1877_, 1, v_inst_1869_);
v___x_1878_ = lean_nat_dec_le(v___x_1874_, v___x_1874_);
if (v___x_1878_ == 0)
{
if (v___x_1876_ == 0)
{
lean_dec_ref(v___f_1877_);
lean_dec_ref(v_entries_1872_);
return v_m1_1870_;
}
else
{
size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_of_nat(v___x_1874_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1875_, v___f_1877_, v_entries_1872_, v___x_1879_, v___x_1880_, v_m1_1870_);
return v___x_1881_;
}
}
else
{
size_t v___x_1882_; size_t v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = lean_usize_of_nat(v___x_1874_);
v___x_1884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1875_, v___f_1877_, v_entries_1872_, v___x_1882_, v___x_1883_, v_m1_1870_);
return v___x_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_merge(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_m1_1891_, lean_object* v_m2_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_Internal_IndexMultiMap_merge___redArg(v_inst_1887_, v_inst_1888_, v_m1_1891_, v_m2_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(lean_object* v_inst_1894_, lean_object* v_inst_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1894_, v_inst_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg___boxed(lean_object* v_inst_1897_, lean_object* v_inst_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Std_Internal_IndexMultiMap_instEmptyCollection___redArg(v_inst_1897_, v_inst_1898_);
lean_dec_ref(v_inst_1898_);
lean_dec_ref(v_inst_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection(lean_object* v_00_u03b1_1900_, lean_object* v_00_u03b2_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1902_, v_inst_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_Internal_IndexMultiMap_instEmptyCollection(v_00_u03b1_1905_, v_00_u03b2_1906_, v_inst_1907_, v_inst_1908_);
lean_dec_ref(v_inst_1908_);
lean_dec_ref(v_inst_1907_);
return v_res_1909_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_unsigned_to_nat(0u);
v___x_1912_ = lean_nat_add(v___x_1911_, v___x_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_unsigned_to_nat(4u);
v___x_1914_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0, &l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0_once, _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0);
v___x_1915_ = lean_nat_mul(v___x_1914_, v___x_1913_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v_fst_1919_; lean_object* v___x_1920_; lean_object* v_entries_1921_; lean_object* v_indexes_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2010_; 
v_fst_1919_ = lean_ctor_get(v_x_1918_, 0);
lean_inc(v_fst_1919_);
v___x_1920_ = l_Std_Internal_IndexMultiMap_empty(lean_box(0), lean_box(0), v_inst_1916_, v_inst_1917_);
v_entries_1921_ = lean_ctor_get(v___x_1920_, 0);
v_indexes_1922_ = lean_ctor_get(v___x_1920_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1924_ = v___x_1920_;
v_isShared_1925_ = v_isSharedCheck_2010_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_indexes_1922_);
lean_inc(v_entries_1921_);
lean_dec(v___x_1920_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2010_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_i_1926_; lean_object* v_entries_1927_; lean_object* v___x_1928_; 
v_i_1926_ = lean_array_get_size(v_entries_1921_);
v_entries_1927_ = lean_array_push(v_entries_1921_, v_x_1918_);
lean_inc(v_fst_1919_);
lean_inc_ref(v_inst_1917_);
lean_inc_ref(v_inst_1916_);
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1916_, v_inst_1917_, v_indexes_1922_, v_fst_1919_);
switch(lean_obj_tag(v___x_1928_))
{
case 0:
{
lean_object* v_index_1929_; lean_object* v_value_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_val_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_dec_ref(v_inst_1917_);
lean_dec_ref(v_inst_1916_);
v_index_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_index_1929_);
v_value_1930_ = lean_ctor_get(v___x_1928_, 2);
lean_inc(v_value_1930_);
lean_dec_ref_known(v___x_1928_, 3);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_value_1930_);
v___x_1932_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1926_, v___x_1931_);
v_val_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_val_1933_);
lean_dec(v___x_1932_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1922_, v___x_1934_, v_index_1929_, v_fst_1919_, v_val_1933_);
lean_dec(v_index_1929_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1935_);
lean_ctor_set(v___x_1924_, 0, v_entries_1927_);
v___x_1937_ = v___x_1924_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_entries_1927_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
case 1:
{
lean_object* v_index_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_val_1942_; lean_object* v___y_1944_; lean_object* v_i_1945_; lean_object* v_keyArray_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_index_1939_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_index_1939_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1940_ = lean_box(0);
v___x_1941_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1926_, v___x_1940_);
v_val_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_val_1942_);
lean_dec(v___x_1941_);
v_keyArray_1965_ = lean_ctor_get(v_indexes_1922_, 1);
v___x_1966_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0, &l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0_once, _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0);
v___x_1967_ = lean_array_get_size(v_keyArray_1965_);
v___x_1968_ = lean_nat_dec_lt(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec(v_index_1939_);
goto v___jp_1953_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1969_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1, &l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1_once, _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1);
v___x_1970_ = lean_unsigned_to_nat(3u);
v___x_1971_ = lean_nat_mul(v___x_1967_, v___x_1970_);
v___x_1972_ = lean_nat_dec_le(v___x_1969_, v___x_1971_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec(v_index_1939_);
goto v___jp_1953_;
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1924_);
lean_dec_ref(v_inst_1917_);
lean_dec_ref(v_inst_1916_);
v___x_1973_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_1922_, v___x_1966_, v_index_1939_, v_fst_1919_, v_val_1942_);
lean_dec(v_index_1939_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_entries_1927_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
return v___x_1974_;
}
}
v___jp_1943_:
{
lean_object* v_size_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v_size_1946_ = lean_ctor_get(v___y_1944_, 0);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_size_1946_, v___x_1947_);
v___x_1949_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1944_, v___x_1948_, v_i_1945_, v_fst_1919_, v_val_1942_);
lean_dec(v_i_1945_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1949_);
lean_ctor_set(v___x_1924_, 0, v_entries_1927_);
v___x_1951_ = v___x_1924_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_entries_1927_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
v___jp_1953_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_inc_ref(v_inst_1917_);
lean_inc_ref(v_inst_1916_);
v___x_1954_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1916_, v_inst_1917_, v_indexes_1922_);
lean_inc(v_fst_1919_);
v___x_1955_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1916_, v_inst_1917_, v___x_1954_, v_fst_1919_);
switch(lean_obj_tag(v___x_1955_))
{
case 0:
{
lean_object* v_index_1956_; lean_object* v_size_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
lean_del_object(v___x_1924_);
v_index_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_index_1956_);
lean_dec_ref_known(v___x_1955_, 3);
v_size_1957_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_size_1957_);
v___x_1958_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1954_, v_size_1957_, v_index_1956_, v_fst_1919_, v_val_1942_);
lean_dec(v_index_1956_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_entries_1927_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
return v___x_1959_;
}
case 1:
{
lean_object* v_index_1960_; 
v_index_1960_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_index_1960_);
lean_dec_ref_known(v___x_1955_, 1);
v___y_1944_ = v___x_1954_;
v_i_1945_ = v_index_1960_;
goto v___jp_1943_;
}
default: 
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1954_, v___x_1961_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_index_1963_; 
v_index_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_index_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___y_1944_ = v___x_1954_;
v_i_1945_ = v_index_1963_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_1964_; 
lean_dec(v_val_1942_);
lean_del_object(v___x_1924_);
lean_dec(v_fst_1919_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_entries_1927_);
lean_ctor_set(v___x_1964_, 1, v___x_1954_);
return v___x_1964_;
}
}
}
}
}
default: 
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_val_1977_; lean_object* v___y_1979_; lean_object* v_i_1980_; lean_object* v___y_1989_; lean_object* v_keyArray_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_1975_ = lean_box(0);
v___x_1976_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_1926_, v___x_1975_);
v_val_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_val_1977_);
lean_dec(v___x_1976_);
v_keyArray_2000_ = lean_ctor_get(v_indexes_1922_, 1);
v___x_2001_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0, &l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0_once, _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__0);
v___x_2002_ = lean_array_get_size(v_keyArray_2000_);
v___x_2003_ = lean_nat_dec_lt(v___x_2001_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; 
lean_inc_ref(v_inst_1917_);
lean_inc_ref(v_inst_1916_);
v___x_2004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1916_, v_inst_1917_, v_indexes_1922_);
v___y_1989_ = v___x_2004_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v___x_2005_ = lean_obj_once(&l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1, &l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1_once, _init_l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1___closed__1);
v___x_2006_ = lean_unsigned_to_nat(3u);
v___x_2007_ = lean_nat_mul(v___x_2002_, v___x_2006_);
v___x_2008_ = lean_nat_dec_le(v___x_2005_, v___x_2007_);
lean_dec(v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_inc_ref(v_inst_1917_);
lean_inc_ref(v_inst_1916_);
v___x_2009_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1916_, v_inst_1917_, v_indexes_1922_);
v___y_1989_ = v___x_2009_;
goto v___jp_1988_;
}
else
{
v___y_1989_ = v_indexes_1922_;
goto v___jp_1988_;
}
}
v___jp_1978_:
{
lean_object* v_size_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1986_; 
v_size_1981_ = lean_ctor_get(v___y_1979_, 0);
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_add(v_size_1981_, v___x_1982_);
v___x_1984_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1979_, v___x_1983_, v_i_1980_, v_fst_1919_, v_val_1977_);
lean_dec(v_i_1980_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1984_);
lean_ctor_set(v___x_1924_, 0, v_entries_1927_);
v___x_1986_ = v___x_1924_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_entries_1927_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
v___jp_1988_:
{
lean_object* v___x_1990_; 
lean_inc(v_fst_1919_);
v___x_1990_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1916_, v_inst_1917_, v___y_1989_, v_fst_1919_);
switch(lean_obj_tag(v___x_1990_))
{
case 0:
{
lean_object* v_index_1991_; lean_object* v_size_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_del_object(v___x_1924_);
v_index_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_index_1991_);
lean_dec_ref_known(v___x_1990_, 3);
v_size_1992_ = lean_ctor_get(v___y_1989_, 0);
lean_inc(v_size_1992_);
v___x_1993_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1989_, v_size_1992_, v_index_1991_, v_fst_1919_, v_val_1977_);
lean_dec(v_index_1991_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v_entries_1927_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
return v___x_1994_;
}
case 1:
{
lean_object* v_index_1995_; 
v_index_1995_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_index_1995_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1979_ = v___y_1989_;
v_i_1980_ = v_index_1995_;
goto v___jp_1978_;
}
default: 
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1989_, v___x_1996_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_index_1998_; 
v_index_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_index_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1979_ = v___y_1989_;
v_i_1980_ = v_index_1998_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1999_; 
lean_dec(v_val_1977_);
lean_del_object(v___x_1924_);
lean_dec(v_fst_1919_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_entries_1927_);
lean_ctor_set(v___x_1999_, 1, v___y_1989_);
return v___x_1999_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_2011_, lean_object* v_inst_2012_){
_start:
{
lean_object* v___f_2013_; 
v___f_2013_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2013_, 0, v_inst_2011_);
lean_closure_set(v___f_2013_, 1, v_inst_2012_);
return v___f_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2014_, lean_object* v_00_u03b2_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_){
_start:
{
lean_object* v___f_2020_; 
v___f_2020_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instSingletonProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2020_, 0, v_inst_2016_);
lean_closure_set(v___f_2020_, 1, v_inst_2017_);
return v___f_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1(lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_x_2023_, lean_object* v_m_2024_){
_start:
{
lean_object* v_fst_2025_; lean_object* v_entries_2026_; lean_object* v_indexes_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2121_; 
v_fst_2025_ = lean_ctor_get(v_x_2023_, 0);
lean_inc(v_fst_2025_);
v_entries_2026_ = lean_ctor_get(v_m_2024_, 0);
v_indexes_2027_ = lean_ctor_get(v_m_2024_, 1);
v_isSharedCheck_2121_ = !lean_is_exclusive(v_m_2024_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2029_ = v_m_2024_;
v_isShared_2030_ = v_isSharedCheck_2121_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_indexes_2027_);
lean_inc(v_entries_2026_);
lean_dec(v_m_2024_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2121_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_i_2031_; lean_object* v_entries_2032_; lean_object* v___x_2033_; 
v_i_2031_ = lean_array_get_size(v_entries_2026_);
v_entries_2032_ = lean_array_push(v_entries_2026_, v_x_2023_);
lean_inc(v_fst_2025_);
lean_inc_ref(v_inst_2022_);
lean_inc_ref(v_inst_2021_);
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2021_, v_inst_2022_, v_indexes_2027_, v_fst_2025_);
switch(lean_obj_tag(v___x_2033_))
{
case 0:
{
lean_object* v_index_2034_; lean_object* v_value_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_val_2038_; lean_object* v_size_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec_ref(v_inst_2022_);
lean_dec_ref(v_inst_2021_);
v_index_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_index_2034_);
v_value_2035_ = lean_ctor_get(v___x_2033_, 2);
lean_inc(v_value_2035_);
lean_dec_ref_known(v___x_2033_, 3);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_value_2035_);
v___x_2037_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_2031_, v___x_2036_);
v_val_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_val_2038_);
lean_dec(v___x_2037_);
v_size_2039_ = lean_ctor_get(v_indexes_2027_, 0);
lean_inc(v_size_2039_);
v___x_2040_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2027_, v_size_2039_, v_index_2034_, v_fst_2025_, v_val_2038_);
lean_dec(v_index_2034_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2040_);
lean_ctor_set(v___x_2029_, 0, v_entries_2032_);
v___x_2042_ = v___x_2029_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_entries_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
case 1:
{
lean_object* v_index_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_val_2047_; lean_object* v___y_2049_; lean_object* v_i_2050_; lean_object* v_size_2070_; lean_object* v_keyArray_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_index_2044_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_index_2044_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2045_ = lean_box(0);
v___x_2046_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_2031_, v___x_2045_);
v_val_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2047_);
lean_dec(v___x_2046_);
v_size_2070_ = lean_ctor_get(v_indexes_2027_, 0);
v_keyArray_2071_ = lean_ctor_get(v_indexes_2027_, 1);
v___x_2072_ = lean_unsigned_to_nat(1u);
v___x_2073_ = lean_nat_add(v_size_2070_, v___x_2072_);
v___x_2074_ = lean_array_get_size(v_keyArray_2071_);
v___x_2075_ = lean_nat_dec_lt(v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_dec(v___x_2073_);
lean_dec(v_index_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2076_ = lean_unsigned_to_nat(4u);
v___x_2077_ = lean_nat_mul(v___x_2073_, v___x_2076_);
v___x_2078_ = lean_unsigned_to_nat(3u);
v___x_2079_ = lean_nat_mul(v___x_2074_, v___x_2078_);
v___x_2080_ = lean_nat_dec_le(v___x_2077_, v___x_2079_);
lean_dec(v___x_2079_);
lean_dec(v___x_2077_);
if (v___x_2080_ == 0)
{
lean_dec(v___x_2073_);
lean_dec(v_index_2044_);
goto v___jp_2058_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_del_object(v___x_2029_);
lean_dec_ref(v_inst_2022_);
lean_dec_ref(v_inst_2021_);
v___x_2081_ = l_Std_DHashMap_Raw_setEntry___redArg(v_indexes_2027_, v___x_2073_, v_index_2044_, v_fst_2025_, v_val_2047_);
lean_dec(v_index_2044_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v_entries_2032_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
return v___x_2082_;
}
}
v___jp_2048_:
{
lean_object* v_size_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v_size_2051_ = lean_ctor_get(v___y_2049_, 0);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_add(v_size_2051_, v___x_2052_);
v___x_2054_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2049_, v___x_2053_, v_i_2050_, v_fst_2025_, v_val_2047_);
lean_dec(v_i_2050_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2054_);
lean_ctor_set(v___x_2029_, 0, v_entries_2032_);
v___x_2056_ = v___x_2029_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_entries_2032_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
v___jp_2058_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_inc_ref(v_inst_2022_);
lean_inc_ref(v_inst_2021_);
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2021_, v_inst_2022_, v_indexes_2027_);
lean_inc(v_fst_2025_);
v___x_2060_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2021_, v_inst_2022_, v___x_2059_, v_fst_2025_);
switch(lean_obj_tag(v___x_2060_))
{
case 0:
{
lean_object* v_index_2061_; lean_object* v_size_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_del_object(v___x_2029_);
v_index_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_index_2061_);
lean_dec_ref_known(v___x_2060_, 3);
v_size_2062_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_size_2062_);
v___x_2063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2059_, v_size_2062_, v_index_2061_, v_fst_2025_, v_val_2047_);
lean_dec(v_index_2061_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_entries_2032_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
return v___x_2064_;
}
case 1:
{
lean_object* v_index_2065_; 
v_index_2065_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_index_2065_);
lean_dec_ref_known(v___x_2060_, 1);
v___y_2049_ = v___x_2059_;
v_i_2050_ = v_index_2065_;
goto v___jp_2048_;
}
default: 
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2059_, v___x_2066_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_index_2068_; 
v_index_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_index_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___y_2049_ = v___x_2059_;
v_i_2050_ = v_index_2068_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2069_; 
lean_dec(v_val_2047_);
lean_del_object(v___x_2029_);
lean_dec(v_fst_2025_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_entries_2032_);
lean_ctor_set(v___x_2069_, 1, v___x_2059_);
return v___x_2069_;
}
}
}
}
}
default: 
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_val_2085_; lean_object* v___y_2087_; lean_object* v_i_2088_; lean_object* v___y_2097_; lean_object* v_size_2108_; lean_object* v_keyArray_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = l_Std_Internal_IndexMultiMap_insert___redArg___lam__0(v_i_2031_, v___x_2083_);
v_val_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_val_2085_);
lean_dec(v___x_2084_);
v_size_2108_ = lean_ctor_get(v_indexes_2027_, 0);
v_keyArray_2109_ = lean_ctor_get(v_indexes_2027_, 1);
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_nat_add(v_size_2108_, v___x_2110_);
v___x_2112_ = lean_array_get_size(v_keyArray_2109_);
v___x_2113_ = lean_nat_dec_lt(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v___x_2111_);
lean_inc_ref(v_inst_2022_);
lean_inc_ref(v_inst_2021_);
v___x_2114_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2021_, v_inst_2022_, v_indexes_2027_);
v___y_2097_ = v___x_2114_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2115_ = lean_unsigned_to_nat(4u);
v___x_2116_ = lean_nat_mul(v___x_2111_, v___x_2115_);
lean_dec(v___x_2111_);
v___x_2117_ = lean_unsigned_to_nat(3u);
v___x_2118_ = lean_nat_mul(v___x_2112_, v___x_2117_);
v___x_2119_ = lean_nat_dec_le(v___x_2116_, v___x_2118_);
lean_dec(v___x_2118_);
lean_dec(v___x_2116_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_inc_ref(v_inst_2022_);
lean_inc_ref(v_inst_2021_);
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2021_, v_inst_2022_, v_indexes_2027_);
v___y_2097_ = v___x_2120_;
goto v___jp_2096_;
}
else
{
v___y_2097_ = v_indexes_2027_;
goto v___jp_2096_;
}
}
v___jp_2086_:
{
lean_object* v_size_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v_size_2089_ = lean_ctor_get(v___y_2087_, 0);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_nat_add(v_size_2089_, v___x_2090_);
v___x_2092_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2087_, v___x_2091_, v_i_2088_, v_fst_2025_, v_val_2085_);
lean_dec(v_i_2088_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 1, v___x_2092_);
lean_ctor_set(v___x_2029_, 0, v_entries_2032_);
v___x_2094_ = v___x_2029_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_entries_2032_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
v___jp_2096_:
{
lean_object* v___x_2098_; 
lean_inc(v_fst_2025_);
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2021_, v_inst_2022_, v___y_2097_, v_fst_2025_);
switch(lean_obj_tag(v___x_2098_))
{
case 0:
{
lean_object* v_index_2099_; lean_object* v_size_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_del_object(v___x_2029_);
v_index_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_index_2099_);
lean_dec_ref_known(v___x_2098_, 3);
v_size_2100_ = lean_ctor_get(v___y_2097_, 0);
lean_inc(v_size_2100_);
v___x_2101_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2097_, v_size_2100_, v_index_2099_, v_fst_2025_, v_val_2085_);
lean_dec(v_index_2099_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_entries_2032_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
return v___x_2102_;
}
case 1:
{
lean_object* v_index_2103_; 
v_index_2103_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_index_2103_);
lean_dec_ref_known(v___x_2098_, 1);
v___y_2087_ = v___y_2097_;
v_i_2088_ = v_index_2103_;
goto v___jp_2086_;
}
default: 
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2097_, v___x_2104_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_index_2106_; 
v_index_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_index_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___y_2087_ = v___y_2097_;
v_i_2088_ = v_index_2106_;
goto v___jp_2086_;
}
else
{
lean_object* v___x_2107_; 
lean_dec(v_val_2085_);
lean_del_object(v___x_2029_);
lean_dec(v_fst_2025_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v_entries_2032_);
lean_ctor_set(v___x_2107_, 1, v___y_2097_);
return v___x_2107_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_2122_, lean_object* v_inst_2123_){
_start:
{
lean_object* v___f_2124_; 
v___f_2124_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2124_, 0, v_inst_2122_);
lean_closure_set(v___f_2124_, 1, v_inst_2123_);
return v___f_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_){
_start:
{
lean_object* v___f_2131_; 
v___f_2131_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instInsertProdOfEquivBEqOfLawfulHashable___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2131_, 0, v_inst_2127_);
lean_closure_set(v___f_2131_, 1, v_inst_2128_);
return v___f_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable___redArg(lean_object* v_inst_2132_, lean_object* v_inst_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_2134_, 0, lean_box(0));
lean_closure_set(v___x_2134_, 1, lean_box(0));
lean_closure_set(v___x_2134_, 2, v_inst_2132_);
lean_closure_set(v___x_2134_, 3, v_inst_2133_);
lean_closure_set(v___x_2134_, 4, lean_box(0));
lean_closure_set(v___x_2134_, 5, lean_box(0));
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instUnionOfEquivBEqOfLawfulHashable(lean_object* v_00_u03b1_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_inst_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_merge), 8, 6);
lean_closure_set(v___x_2141_, 0, lean_box(0));
lean_closure_set(v___x_2141_, 1, lean_box(0));
lean_closure_set(v___x_2141_, 2, v_inst_2137_);
lean_closure_set(v___x_2141_, 3, v_inst_2138_);
lean_closure_set(v___x_2141_, 4, lean_box(0));
lean_closure_set(v___x_2141_, 5, lean_box(0));
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_2142_, lean_object* v_a_2143_, lean_object* v_x_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_apply_2(v_f_2142_, v_a_2143_, v___y_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_2147_, lean_object* v_00_u03b2_2148_, lean_object* v_map_2149_, lean_object* v_b_2150_, lean_object* v_f_2151_){
_start:
{
lean_object* v_entries_2152_; lean_object* v___f_2153_; size_t v_sz_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v_entries_2152_ = lean_ctor_get(v_map_2149_, 0);
lean_inc_ref(v_entries_2152_);
lean_dec_ref(v_map_2149_);
v___f_2153_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2153_, 0, v_f_2151_);
v_sz_2154_ = lean_array_size(v_entries_2152_);
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2147_, v_entries_2152_, v___f_2153_, v_sz_2154_, v___x_2155_, v_b_2150_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg(lean_object* v_inst_2157_){
_start:
{
lean_object* v___f_2158_; 
v___f_2158_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2158_, 0, v_inst_2157_);
return v___f_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad(lean_object* v_00_u03b1_2159_, lean_object* v_00_u03b2_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_m_2163_, lean_object* v_inst_2164_){
_start:
{
lean_object* v___f_2165_; 
v___f_2165_ = lean_alloc_closure((void*)(l_Std_Internal_IndexMultiMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_2165_, 0, v_inst_2164_);
return v___f_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IndexMultiMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_2166_, lean_object* v_00_u03b2_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_m_2170_, lean_object* v_inst_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Std_Internal_IndexMultiMap_instForInProdOfMonad(v_00_u03b1_2166_, v_00_u03b2_2167_, v_inst_2168_, v_inst_2169_, v_m_2170_, v_inst_2171_);
lean_dec_ref(v_inst_2169_);
lean_dec_ref(v_inst_2168_);
return v_res_2172_;
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
