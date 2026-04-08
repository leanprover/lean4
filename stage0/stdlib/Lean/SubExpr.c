// Lean compiler output
// Module: Lean.SubExpr
// Imports: public import Lean.Meta.Basic public import Init.Data.Format.Macro
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
lean_object* l_Lean_Name_fromJson_x3f(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getTag_x3f(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_parseCtorFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_instOrdNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_maxChildren;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_typeCoord;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_root;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instInhabited;
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_head_spec__0(lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.SubExpr"};
static const lean_object* l_Lean_SubExpr_Pos_head___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_head___closed__0_value;
static const lean_string_object l_Lean_SubExpr_Pos_head___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.SubExpr.Pos.head"};
static const lean_object* l_Lean_SubExpr_Pos_head___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_head___closed__1_value;
static const lean_string_object l_Lean_SubExpr_Pos_head___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "already at top"};
static const lean_object* l_Lean_SubExpr_Pos_head___closed__2 = (const lean_object*)&l_Lean_SubExpr_Pos_head___closed__2_value;
static lean_once_cell_t l_Lean_SubExpr_Pos_head___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_Pos_head___closed__3;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_tail___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.SubExpr.Pos.tail"};
static const lean_object* l_Lean_SubExpr_Pos_tail___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_tail___closed__0_value;
static lean_once_cell_t l_Lean_SubExpr_Pos_tail___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_Pos_tail___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail___boxed(lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_push___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.SubExpr.Pos.push"};
static const lean_object* l_Lean_SubExpr_Pos_push___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_push___closed__0_value;
static const lean_string_object l_Lean_SubExpr_Pos_push___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "invalid coordinate "};
static const lean_object* l_Lean_SubExpr_Pos_push___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_push___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_depth___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_depth___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_depth___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_depth___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_append___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_push___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_append___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_append___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_toArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_push___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_SubExpr_Pos_toArray___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_toArray___closed__0_value;
static const lean_array_object l_Lean_SubExpr_Pos_toArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_SubExpr_Pos_toArray___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_toArray___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lean_SubExpr_Pos_toString___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString___boxed(lean_object*);
static const lean_string_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0_value;
static const lean_string_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1_value;
static const lean_string_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2_value;
static const lean_string_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3_value;
static const lean_string_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Invalid coordinate "};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4_value;
static const lean_ctor_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5_value;
static const lean_ctor_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6_value;
static const lean_ctor_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7_value;
static const lean_ctor_object l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8 = (const lean_object*)&l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_fromString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "malformed "};
static const lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_fromString_x3f___closed__0_value;
static const lean_array_object l_Lean_SubExpr_Pos_fromString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_fromString_x3f___closed__1_value;
static const lean_string_object l_Lean_SubExpr_Pos_fromString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_SubExpr_Pos_fromString_x3f___closed__2 = (const lean_object*)&l_Lean_SubExpr_Pos_fromString_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SubExpr_Pos_fromString_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.SubExpr.Pos.fromString!"};
static const lean_object* l_Lean_SubExpr_Pos_fromString_x21___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_fromString_x21___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instOrdNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_instOrd___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_Pos_instOrd = (const lean_object*)&l_Lean_SubExpr_Pos_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_instToString___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_Pos_instToString = (const lean_object*)&l_Lean_SubExpr_Pos_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instEmptyCollection;
static const lean_string_object l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Pos.fromString! "};
static const lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_instRepr___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_Pos_instRepr = (const lean_object*)&l_Lean_SubExpr_Pos_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_instToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_instToJson___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instToJson___closed__0_value;
static const lean_closure_object l_Lean_SubExpr_Pos_instToJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SubExpr_Pos_instToJson___closed__0_value),((lean_object*)&l_Lean_SubExpr_Pos_instToString___closed__0_value)} };
static const lean_object* l_Lean_SubExpr_Pos_instToJson___closed__1 = (const lean_object*)&l_Lean_SubExpr_Pos_instToJson___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_Pos_instToJson = (const lean_object*)&l_Lean_SubExpr_Pos_instToJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_SubExpr_Pos_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_Pos_instFromJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_Pos_instFromJson___closed__0 = (const lean_object*)&l_Lean_SubExpr_Pos_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_Pos_instFromJson = (const lean_object*)&l_Lean_SubExpr_Pos_instFromJson___closed__0_value;
static const lean_string_object l_Lean_instInhabitedSubExpr_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedSubExpr_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedSubExpr_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedSubExpr_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedSubExpr_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedSubExpr_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedSubExpr_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedSubExpr_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedSubExpr_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedSubExpr_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedSubExpr_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedSubExpr_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedSubExpr;
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_SubExpr_bindingBody_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.SubExpr.bindingBody!"};
static const lean_object* l_Lean_SubExpr_bindingBody_x21___closed__0 = (const lean_object*)&l_Lean_SubExpr_bindingBody_x21___closed__0_value;
static const lean_string_object l_Lean_SubExpr_bindingBody_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "subexpr is not a binder"};
static const lean_object* l_Lean_SubExpr_bindingBody_x21___closed__1 = (const lean_object*)&l_Lean_SubExpr_bindingBody_x21___closed__1_value;
static lean_once_cell_t l_Lean_SubExpr_bindingBody_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_bindingBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object*);
static const lean_string_object l_Lean_SubExpr_bindingDomain_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.SubExpr.bindingDomain!"};
static const lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__0 = (const lean_object*)&l_Lean_SubExpr_bindingDomain_x21___closed__0_value;
static lean_once_cell_t l_Lean_SubExpr_bindingDomain_x21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_bindingDomain_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instToJsonFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instToJsonFVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instToJsonFVarId___closed__0 = (const lean_object*)&l_Lean_SubExpr_instToJsonFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instToJsonFVarId = (const lean_object*)&l_Lean_SubExpr_instToJsonFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instToJsonMVarId = (const lean_object*)&l_Lean_SubExpr_instToJsonFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instFromJsonFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instFromJsonFVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instFromJsonFVarId___closed__0 = (const lean_object*)&l_Lean_SubExpr_instFromJsonFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instFromJsonFVarId = (const lean_object*)&l_Lean_SubExpr_instFromJsonFVarId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instFromJsonMVarId = (const lean_object*)&l_Lean_SubExpr_instFromJsonFVarId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "no inductive tag found"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value)}};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "target"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hyp"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hypType"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hypValue"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "no inductive constructor matched"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value)}};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instFromJsonGoalLocation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation___closed__0 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instFromJsonGoalLocation = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalLocation_toJson(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instToJsonGoalLocation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instToJsonGoalLocation___closed__0 = (const lean_object*)&l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instToJsonGoalLocation = (const lean_object*)&l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvarId"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SubExpr"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "GoalsLocation"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value;
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_0),((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(170, 131, 175, 90, 105, 49, 153, 209)}};
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_1),((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(156, 32, 46, 203, 174, 149, 194, 69)}};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7;
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 8, 121, 101, 233, 69, 204, 89)}};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12;
static const lean_string_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "loc"};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value;
static const lean_ctor_object l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 214, 13, 195, 223, 166, 82, 163)}};
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16;
static lean_once_cell_t l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0 = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation = (const lean_object*)&l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(lean_object*, lean_object*);
static const lean_array_object l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0 = (const lean_object*)&l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalsLocation_toJson(lean_object*);
static const lean_closure_object l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SubExpr_instToJsonGoalsLocation_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SubExpr_instToJsonGoalsLocation___closed__0 = (const lean_object*)&l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_SubExpr_instToJsonGoalsLocation = (const lean_object*)&l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_SubExpr_Pos_maxChildren(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(4u);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_typeCoord(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(3u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat(lean_object* v_a_3_){
_start:
{
lean_inc(v_a_3_);
return v_a_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_asNat___boxed(lean_object* v_a_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_SubExpr_Pos_asNat(v_a_4_);
lean_dec(v_a_4_);
return v_res_5_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_root(void){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(1u);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instInhabited(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(1u);
return v___x_7_;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object* v_p_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(4u);
v___x_10_ = lean_nat_dec_lt(v_p_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object* v_p_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lean_SubExpr_Pos_isRoot(v_p_11_);
lean_dec(v_p_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_head_spec__0(lean_object* v_msg_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_panic_fn_borrowed(v___x_15_, v_msg_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__2));
v___x_21_ = lean_unsigned_to_nat(19u);
v___x_22_ = lean_unsigned_to_nat(46u);
v___x_23_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__1));
v___x_24_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_25_ = l_mkPanicMessageWithDecl(v___x_24_, v___x_23_, v___x_22_, v___x_21_, v___x_20_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object* v_p_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l_Lean_SubExpr_Pos_isRoot(v_p_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(4u);
v___x_29_ = lean_nat_mod(v_p_26_, v___x_28_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_obj_once(&l_Lean_SubExpr_Pos_head___closed__3, &l_Lean_SubExpr_Pos_head___closed__3_once, _init_l_Lean_SubExpr_Pos_head___closed__3);
v___x_31_ = l_panic___at___00Lean_SubExpr_Pos_head_spec__0(v___x_30_);
return v___x_31_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object* v_p_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_SubExpr_Pos_head(v_p_32_);
lean_dec(v_p_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(lean_object* v_msg_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_panic_fn_borrowed(v___x_35_, v_msg_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__1(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_38_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__2));
v___x_39_ = lean_unsigned_to_nat(19u);
v___x_40_ = lean_unsigned_to_nat(50u);
v___x_41_ = ((lean_object*)(l_Lean_SubExpr_Pos_tail___closed__0));
v___x_42_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_43_ = l_mkPanicMessageWithDecl(v___x_42_, v___x_41_, v___x_40_, v___x_39_, v___x_38_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object* v_p_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = l_Lean_SubExpr_Pos_isRoot(v_p_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = l_Lean_SubExpr_Pos_head(v_p_44_);
v___x_47_ = lean_nat_sub(v_p_44_, v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = lean_unsigned_to_nat(2u);
v___x_49_ = lean_nat_shiftr(v___x_47_, v___x_48_);
lean_dec(v___x_47_);
return v___x_49_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_SubExpr_Pos_tail___closed__1, &l_Lean_SubExpr_Pos_tail___closed__1_once, _init_l_Lean_SubExpr_Pos_tail___closed__1);
v___x_51_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail___boxed(lean_object* v_p_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_SubExpr_Pos_tail(v_p_52_);
lean_dec(v_p_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object* v_p_56_, lean_object* v_c_57_){
_start:
{
lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(4u);
v___x_59_ = lean_nat_dec_le(v___x_58_, v_c_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_nat_mul(v_p_56_, v___x_58_);
v___x_61_ = lean_nat_add(v___x_60_, v_c_57_);
lean_dec(v_c_57_);
lean_dec(v___x_60_);
return v___x_61_;
}
else
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_62_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_63_ = ((lean_object*)(l_Lean_SubExpr_Pos_push___closed__0));
v___x_64_ = lean_unsigned_to_nat(54u);
v___x_65_ = lean_unsigned_to_nat(27u);
v___x_66_ = ((lean_object*)(l_Lean_SubExpr_Pos_push___closed__1));
v___x_67_ = l_Nat_reprFast(v_c_57_);
v___x_68_ = lean_string_append(v___x_66_, v___x_67_);
lean_dec_ref(v___x_67_);
v___x_69_ = l_mkPanicMessageWithDecl(v___x_62_, v___x_63_, v___x_64_, v___x_65_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object* v_p_71_, lean_object* v_c_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_SubExpr_Pos_push(v_p_71_, v_c_72_);
lean_dec(v_p_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg(lean_object* v_f_74_, lean_object* v_init_75_, lean_object* v_p_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = l_Lean_SubExpr_Pos_isRoot(v_p_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = l_Lean_SubExpr_Pos_tail(v_p_76_);
lean_inc(v_f_74_);
v___x_79_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_74_, v_init_75_, v___x_78_);
lean_dec(v___x_78_);
v___x_80_ = l_Lean_SubExpr_Pos_head(v_p_76_);
v___x_81_ = lean_apply_2(v_f_74_, v___x_79_, v___x_80_);
return v___x_81_;
}
else
{
lean_dec(v_f_74_);
lean_inc(v_init_75_);
return v_init_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg___boxed(lean_object* v_f_82_, lean_object* v_init_83_, lean_object* v_p_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_82_, v_init_83_, v_p_84_);
lean_dec(v_p_84_);
lean_dec(v_init_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object* v_00_u03b1_86_, lean_object* v_f_87_, lean_object* v_init_88_, lean_object* v_p_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_87_, v_init_88_, v_p_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___boxed(lean_object* v_00_u03b1_91_, lean_object* v_f_92_, lean_object* v_init_93_, lean_object* v_p_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_SubExpr_Pos_foldl(v_00_u03b1_91_, v_f_92_, v_init_93_, v_p_94_);
lean_dec(v_p_94_);
lean_dec(v_init_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___redArg(lean_object* v_f_96_, lean_object* v_p_97_, lean_object* v_init_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_SubExpr_Pos_isRoot(v_p_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_Lean_SubExpr_Pos_tail(v_p_97_);
v___x_101_ = l_Lean_SubExpr_Pos_head(v_p_97_);
lean_dec(v_p_97_);
lean_inc(v_f_96_);
v___x_102_ = lean_apply_2(v_f_96_, v___x_101_, v_init_98_);
v_p_97_ = v___x_100_;
v_init_98_ = v___x_102_;
goto _start;
}
else
{
lean_dec(v_p_97_);
lean_dec(v_f_96_);
return v_init_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object* v_00_u03b1_104_, lean_object* v_f_105_, lean_object* v_p_106_, lean_object* v_init_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_SubExpr_Pos_foldr___redArg(v_f_105_, v_p_106_, v_init_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(lean_object* v_p_109_, lean_object* v_f_110_, lean_object* v_x_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = l_Lean_SubExpr_Pos_head(v_p_109_);
v___x_113_ = lean_apply_2(v_f_110_, v_x_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed(lean_object* v_p_114_, lean_object* v_f_115_, lean_object* v_x_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(v_p_114_, v_f_115_, v_x_116_);
lean_dec(v_p_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg(lean_object* v_inst_118_, lean_object* v_f_119_, lean_object* v_init_120_, lean_object* v_p_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = l_Lean_SubExpr_Pos_isRoot(v_p_121_);
if (v___x_122_ == 0)
{
lean_object* v_toBind_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_toBind_123_ = lean_ctor_get(v_inst_118_, 1);
lean_inc(v_toBind_123_);
lean_inc(v_f_119_);
lean_inc(v_p_121_);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_124_, 0, v_p_121_);
lean_closure_set(v___f_124_, 1, v_f_119_);
v___x_125_ = l_Lean_SubExpr_Pos_tail(v_p_121_);
lean_dec(v_p_121_);
v___x_126_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_118_, v_f_119_, v_init_120_, v___x_125_);
v___x_127_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_126_, v___f_124_);
return v___x_127_;
}
else
{
lean_object* v_toApplicative_128_; lean_object* v_toPure_129_; lean_object* v___x_130_; 
lean_dec(v_p_121_);
lean_dec(v_f_119_);
v_toApplicative_128_ = lean_ctor_get(v_inst_118_, 0);
lean_inc_ref(v_toApplicative_128_);
lean_dec_ref(v_inst_118_);
v_toPure_129_ = lean_ctor_get(v_toApplicative_128_, 1);
lean_inc(v_toPure_129_);
lean_dec_ref(v_toApplicative_128_);
v___x_130_ = lean_apply_2(v_toPure_129_, lean_box(0), v_init_120_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_M_133_, lean_object* v_inst_134_, lean_object* v_f_135_, lean_object* v_init_136_, lean_object* v_p_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_134_, v_f_135_, v_init_136_, v_p_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___boxed(lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_M_141_, lean_object* v_inst_142_, lean_object* v_f_143_, lean_object* v_init_144_, lean_object* v_p_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_SubExpr_Pos_foldlM(v_00_u03b1_139_, v_inst_140_, v_M_141_, v_inst_142_, v_f_143_, v_init_144_, v_p_145_);
lean_dec(v_inst_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg___boxed(lean_object* v_inst_147_, lean_object* v_f_148_, lean_object* v_p_149_, lean_object* v_init_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_147_, v_f_148_, v_p_149_, v_init_150_);
lean_dec(v_p_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg(lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_p_154_, lean_object* v_init_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_SubExpr_Pos_isRoot(v_p_154_);
if (v___x_156_ == 0)
{
lean_object* v_toBind_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_toBind_157_ = lean_ctor_get(v_inst_152_, 1);
lean_inc(v_toBind_157_);
v___x_158_ = l_Lean_SubExpr_Pos_head(v_p_154_);
lean_inc(v_f_153_);
v___x_159_ = lean_apply_2(v_f_153_, v___x_158_, v_init_155_);
v___x_160_ = l_Lean_SubExpr_Pos_tail(v_p_154_);
v___x_161_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___redArg___boxed), 4, 3);
lean_closure_set(v___x_161_, 0, v_inst_152_);
lean_closure_set(v___x_161_, 1, v_f_153_);
lean_closure_set(v___x_161_, 2, v___x_160_);
v___x_162_ = lean_apply_4(v_toBind_157_, lean_box(0), lean_box(0), v___x_159_, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v_toApplicative_163_; lean_object* v_toPure_164_; lean_object* v___x_165_; 
lean_dec(v_f_153_);
v_toApplicative_163_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toApplicative_163_);
lean_dec_ref(v_inst_152_);
v_toPure_164_ = lean_ctor_get(v_toApplicative_163_, 1);
lean_inc(v_toPure_164_);
lean_dec_ref(v_toApplicative_163_);
v___x_165_ = lean_apply_2(v_toPure_164_, lean_box(0), v_init_155_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object* v_00_u03b1_166_, lean_object* v_M_167_, lean_object* v_inst_168_, lean_object* v_f_169_, lean_object* v_p_170_, lean_object* v_init_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_168_, v_f_169_, v_p_170_, v_init_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___boxed(lean_object* v_00_u03b1_173_, lean_object* v_M_174_, lean_object* v_inst_175_, lean_object* v_f_176_, lean_object* v_p_177_, lean_object* v_init_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_SubExpr_Pos_foldrM(v_00_u03b1_173_, v_M_174_, v_inst_175_, v_f_176_, v_p_177_, v_init_178_);
lean_dec(v_p_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0(lean_object* v_x_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v___y_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0___boxed(lean_object* v_x_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_SubExpr_Pos_depth___lam__0(v_x_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec(v_x_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object* v_p_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___f_189_ = ((lean_object*)(l_Lean_SubExpr_Pos_depth___closed__0));
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = l_Lean_SubExpr_Pos_foldr___redArg(v___f_189_, v_p_188_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lam__0(lean_object* v_pred_192_, lean_object* v_n_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_apply_1(v_pred_192_, v_n_193_);
v___x_196_ = lean_unbox(v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_198_, 0, v_a_194_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(lean_object* v_f_199_, lean_object* v_p_200_, lean_object* v_init_201_){
_start:
{
uint8_t v___x_202_; 
v___x_202_ = l_Lean_SubExpr_Pos_isRoot(v_p_200_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = l_Lean_SubExpr_Pos_head(v_p_200_);
lean_inc_ref(v_f_199_);
v___x_204_ = lean_apply_2(v_f_199_, v___x_203_, v_init_201_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_dec(v_p_200_);
lean_dec_ref(v_f_199_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v___x_204_);
v___x_206_ = l_Lean_SubExpr_Pos_tail(v_p_200_);
lean_dec(v_p_200_);
v_p_200_ = v___x_206_;
v_init_201_ = v_val_205_;
goto _start;
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v_p_200_);
lean_dec_ref(v_f_199_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_init_201_);
return v___x_208_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_all(lean_object* v_pred_209_, lean_object* v_p_210_){
_start:
{
lean_object* v___f_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___f_211_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_all___lam__0), 3, 1);
lean_closure_set(v___f_211_, 0, v_pred_209_);
v___x_212_ = lean_box(0);
v___x_213_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(v___f_211_, v_p_210_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
uint8_t v___x_214_; 
v___x_214_ = 0;
return v___x_214_;
}
else
{
uint8_t v___x_215_; 
lean_dec_ref(v___x_213_);
v___x_215_ = 1;
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object* v_pred_216_, lean_object* v_p_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Lean_SubExpr_Pos_all(v_pred_216_, v_p_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0(lean_object* v_00_u03b1_220_, lean_object* v_f_221_, lean_object* v_p_222_, lean_object* v_init_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(v_f_221_, v_p_222_, v_init_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object* v_init_226_, lean_object* v_p_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = ((lean_object*)(l_Lean_SubExpr_Pos_append___closed__0));
v___x_229_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_228_, v_init_226_, v_p_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object* v_init_230_, lean_object* v_p_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_SubExpr_Pos_append(v_init_230_, v_p_231_);
lean_dec(v_p_231_);
lean_dec(v_init_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(lean_object* v_as_233_, size_t v_i_234_, size_t v_stop_235_, lean_object* v_b_236_){
_start:
{
uint8_t v___x_237_; 
v___x_237_ = lean_usize_dec_eq(v_i_234_, v_stop_235_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; size_t v___x_240_; size_t v___x_241_; 
v___x_238_ = lean_array_uget_borrowed(v_as_233_, v_i_234_);
lean_inc(v___x_238_);
v___x_239_ = l_Lean_SubExpr_Pos_push(v_b_236_, v___x_238_);
lean_dec(v_b_236_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_i_234_, v___x_240_);
v_i_234_ = v___x_241_;
v_b_236_ = v___x_239_;
goto _start;
}
else
{
return v_b_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0___boxed(lean_object* v_as_243_, lean_object* v_i_244_, lean_object* v_stop_245_, lean_object* v_b_246_){
_start:
{
size_t v_i_boxed_247_; size_t v_stop_boxed_248_; lean_object* v_res_249_; 
v_i_boxed_247_ = lean_unbox_usize(v_i_244_);
lean_dec(v_i_244_);
v_stop_boxed_248_ = lean_unbox_usize(v_stop_245_);
lean_dec(v_stop_245_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_as_243_, v_i_boxed_247_, v_stop_boxed_248_, v_b_246_);
lean_dec_ref(v_as_243_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object* v_ps_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = lean_array_get_size(v_ps_250_);
v___x_254_ = lean_nat_dec_lt(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
return v___x_251_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_le(v___x_253_, v___x_253_);
if (v___x_255_ == 0)
{
if (v___x_254_ == 0)
{
return v___x_251_;
}
else
{
size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((size_t)0ULL);
v___x_257_ = lean_usize_of_nat(v___x_253_);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_250_, v___x_256_, v___x_257_, v___x_251_);
return v___x_258_;
}
}
else
{
size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_253_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_250_, v___x_259_, v___x_260_, v___x_251_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object* v_ps_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_SubExpr_Pos_ofArray(v_ps_262_);
lean_dec_ref(v_ps_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object* v_p_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l_Lean_SubExpr_Pos_toArray___closed__0));
v___x_269_ = ((lean_object*)(l_Lean_SubExpr_Pos_toArray___closed__1));
v___x_270_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_268_, v___x_269_, v_p_267_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray___boxed(lean_object* v_p_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_SubExpr_Pos_toArray(v_p_271_);
lean_dec(v_p_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object* v_p_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = l_Lean_SubExpr_Pos_push(v_p_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object* v_p_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_276_);
lean_dec(v_p_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object* v_p_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = l_Lean_SubExpr_Pos_push(v_p_278_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object* v_p_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_281_);
lean_dec(v_p_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object* v_p_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = l_Lean_SubExpr_Pos_push(v_p_283_, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object* v_p_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_286_);
lean_dec(v_p_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object* v_p_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = l_Lean_SubExpr_Pos_push(v_p_288_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object* v_p_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_291_);
lean_dec(v_p_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object* v_p_293_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(2u);
v___x_295_ = l_Lean_SubExpr_Pos_push(v_p_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object* v_p_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_296_);
lean_dec(v_p_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object* v_p_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Lean_SubExpr_Pos_push(v_p_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object* v_p_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_301_);
lean_dec(v_p_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object* v_p_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = l_Lean_SubExpr_Pos_push(v_p_303_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object* v_p_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_306_);
lean_dec(v_p_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object* v_p_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = l_Lean_SubExpr_Pos_push(v_p_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object* v_p_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_SubExpr_Pos_pushProj(v_p_311_);
lean_dec(v_p_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType(lean_object* v_p_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = l_Lean_SubExpr_Pos_push(v_p_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType___boxed(lean_object* v_p_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_SubExpr_Pos_pushType(v_p_316_);
lean_dec(v_p_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object* v_numArgs_318_, lean_object* v_p_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(4u);
v___x_321_ = lean_nat_pow(v___x_320_, v_numArgs_318_);
v___x_322_ = lean_nat_mul(v_p_319_, v___x_321_);
lean_dec(v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object* v_numArgs_323_, lean_object* v_p_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_SubExpr_Pos_pushNaryFn(v_numArgs_323_, v_p_324_);
lean_dec(v_p_324_);
lean_dec(v_numArgs_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object* v_numArgs_326_, lean_object* v_argIdx_327_, lean_object* v_p_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_this_334_; 
v___x_329_ = lean_unsigned_to_nat(4u);
v___x_330_ = lean_nat_sub(v_numArgs_326_, v_argIdx_327_);
v___x_331_ = lean_nat_pow(v___x_329_, v___x_330_);
lean_dec(v___x_330_);
v___x_332_ = lean_nat_mul(v_p_328_, v___x_331_);
lean_dec(v___x_331_);
v___x_333_ = lean_unsigned_to_nat(1u);
v_this_334_ = lean_nat_add(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
return v_this_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object* v_numArgs_335_, lean_object* v_argIdx_336_, lean_object* v_p_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_SubExpr_Pos_pushNaryArg(v_numArgs_335_, v_argIdx_336_, v_p_337_);
lean_dec(v_p_337_);
lean_dec(v_argIdx_336_);
lean_dec(v_numArgs_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v_zero_341_; uint8_t v_isZero_342_; 
v_zero_341_ = lean_unsigned_to_nat(0u);
v_isZero_342_ = lean_nat_dec_eq(v_x_339_, v_zero_341_);
if (v_isZero_342_ == 1)
{
lean_object* v___x_343_; 
lean_dec(v_x_339_);
v___x_343_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_x_340_);
lean_dec(v_x_340_);
return v___x_343_;
}
else
{
lean_object* v_one_344_; lean_object* v_n_345_; lean_object* v___x_346_; 
v_one_344_ = lean_unsigned_to_nat(1u);
v_n_345_ = lean_nat_sub(v_x_339_, v_one_344_);
lean_dec(v_x_339_);
v___x_346_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_340_);
lean_dec(v_x_340_);
v_x_339_ = v_n_345_;
v_x_340_ = v___x_346_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_zero_350_; uint8_t v_isZero_351_; 
v_zero_350_ = lean_unsigned_to_nat(0u);
v_isZero_351_ = lean_nat_dec_eq(v_x_348_, v_zero_350_);
if (v_isZero_351_ == 1)
{
lean_dec(v_x_348_);
return v_x_349_;
}
else
{
lean_object* v_one_352_; lean_object* v_n_353_; lean_object* v___x_354_; 
v_one_352_ = lean_unsigned_to_nat(1u);
v_n_353_ = lean_nat_sub(v_x_348_, v_one_352_);
lean_dec(v_x_348_);
v___x_354_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_349_);
lean_dec(v_x_349_);
v_x_348_ = v_n_353_;
v_x_349_ = v___x_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
if (lean_obj_tag(v_a_356_) == 0)
{
lean_object* v___x_358_; 
v___x_358_ = l_List_reverse___redArg(v_a_357_);
return v___x_358_;
}
else
{
lean_object* v_head_359_; lean_object* v_tail_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_369_; 
v_head_359_ = lean_ctor_get(v_a_356_, 0);
v_tail_360_ = lean_ctor_get(v_a_356_, 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_356_);
if (v_isSharedCheck_369_ == 0)
{
v___x_362_ = v_a_356_;
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_tail_360_);
lean_inc(v_head_359_);
lean_dec(v_a_356_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = l_Nat_reprFast(v_head_359_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_a_357_);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_a_357_);
v___x_366_ = v_reuseFailAlloc_368_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v_a_356_ = v_tail_360_;
v_a_357_ = v___x_366_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object* v_p_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_372_ = ((lean_object*)(l_Lean_SubExpr_Pos_toString___closed__0));
v___x_373_ = l_Lean_SubExpr_Pos_toArray(v_p_371_);
v___x_374_ = lean_array_to_list(v___x_373_);
v___x_375_ = lean_box(0);
v___x_376_ = l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(v___x_374_, v___x_375_);
v___x_377_ = l_String_intercalate(v___x_372_, v___x_376_);
v___x_378_ = lean_string_append(v___x_372_, v___x_377_);
lean_dec_ref(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString___boxed(lean_object* v_p_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_SubExpr_Pos_toString(v_p_379_);
lean_dec(v_p_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object* v_x_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0));
v___x_396_ = lean_string_dec_eq(v_x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1));
v___x_398_ = lean_string_dec_eq(v_x_394_, v___x_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2));
v___x_400_ = lean_string_dec_eq(v_x_394_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3));
v___x_402_ = lean_string_dec_eq(v_x_394_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4));
v___x_404_ = lean_string_append(v___x_403_, v_x_394_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5));
return v___x_406_;
}
}
else
{
lean_object* v___x_407_; 
v___x_407_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6));
return v___x_407_;
}
}
else
{
lean_object* v___x_408_; 
v___x_408_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7));
return v___x_408_;
}
}
else
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8));
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_x_410_);
lean_dec_ref(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(lean_object* v_s_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0));
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___boxed(lean_object* v_s_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v_s_416_);
lean_dec_ref(v_s_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(size_t v_sz_418_, size_t v_i_419_, lean_object* v_bs_420_){
_start:
{
uint8_t v___x_421_; 
v___x_421_ = lean_usize_dec_lt(v_i_419_, v_sz_418_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_422_, 0, v_bs_420_);
return v___x_422_;
}
else
{
lean_object* v_v_423_; lean_object* v___x_424_; 
v_v_423_ = lean_array_uget_borrowed(v_bs_420_, v_i_419_);
v___x_424_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_v_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_bs_420_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
else
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v_bs_x27_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v_a_433_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v___x_424_);
v___x_434_ = lean_unsigned_to_nat(0u);
v_bs_x27_435_ = lean_array_uset(v_bs_420_, v_i_419_, v___x_434_);
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_419_, v___x_436_);
v___x_438_ = lean_array_uset(v_bs_x27_435_, v_i_419_, v_a_433_);
v_i_419_ = v___x_437_;
v_bs_420_ = v___x_438_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3___boxed(lean_object* v_sz_440_, lean_object* v_i_441_, lean_object* v_bs_442_){
_start:
{
size_t v_sz_boxed_443_; size_t v_i_boxed_444_; lean_object* v_res_445_; 
v_sz_boxed_443_ = lean_unbox_usize(v_sz_440_);
lean_dec(v_sz_440_);
v_i_boxed_444_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_boxed_443_, v_i_boxed_444_, v_bs_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
return v_x_447_;
}
else
{
lean_object* v_head_449_; lean_object* v_tail_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_head_449_ = lean_ctor_get(v_x_448_, 0);
v_tail_450_ = lean_ctor_get(v_x_448_, 1);
v___x_451_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0));
v___x_452_ = lean_string_append(v_x_447_, v___x_451_);
v___x_453_ = lean_string_append(v___x_452_, v_head_449_);
v_x_447_ = v___x_453_;
v_x_448_ = v_tail_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v_x_455_, v_x_456_);
lean_dec(v_x_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(lean_object* v_x_461_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0));
return v___x_462_;
}
else
{
lean_object* v_tail_463_; 
v_tail_463_ = lean_ctor_get(v_x_461_, 1);
if (lean_obj_tag(v_tail_463_) == 0)
{
lean_object* v_head_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_head_464_ = lean_ctor_get(v_x_461_, 0);
v___x_465_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_466_ = lean_string_append(v___x_465_, v_head_464_);
v___x_467_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2));
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v_head_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint32_t v___x_473_; lean_object* v___x_474_; 
v_head_469_ = lean_ctor_get(v_x_461_, 0);
v___x_470_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_471_ = lean_string_append(v___x_470_, v_head_469_);
v___x_472_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v___x_471_, v_tail_463_);
v___x_473_ = 93;
v___x_474_ = lean_string_push(v___x_472_, v___x_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___boxed(lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_x_475_);
lean_dec(v_x_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(lean_object* v_x_477_, lean_object* v___x_478_, lean_object* v___x_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v_it_483_; lean_object* v_startInclusive_484_; lean_object* v_endExclusive_485_; 
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v_currPos_490_; lean_object* v_searcher_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_517_; 
v_currPos_490_ = lean_ctor_get(v_a_480_, 0);
v_searcher_491_ = lean_ctor_get(v_a_480_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_517_ == 0)
{
v___x_493_ = v_a_480_;
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_searcher_491_);
lean_inc(v_currPos_490_);
lean_dec(v_a_480_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_startInclusive_495_; lean_object* v_endExclusive_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_startInclusive_495_ = lean_ctor_get(v___x_478_, 1);
v_endExclusive_496_ = lean_ctor_get(v___x_478_, 2);
v___x_497_ = lean_nat_sub(v_endExclusive_496_, v_startInclusive_495_);
v___x_498_ = lean_nat_dec_eq(v_searcher_491_, v___x_497_);
lean_dec(v___x_497_);
if (v___x_498_ == 0)
{
uint32_t v___x_499_; uint32_t v___x_500_; uint8_t v___x_501_; 
v___x_499_ = 47;
v___x_500_ = lean_string_utf8_get_fast(v_x_477_, v_searcher_491_);
v___x_501_ = lean_uint32_dec_eq(v___x_500_, v___x_499_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_string_utf8_next_fast(v_x_477_, v_searcher_491_);
lean_dec(v_searcher_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_502_);
v___x_504_ = v___x_493_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_currPos_490_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v___x_502_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v_a_480_ = v___x_504_;
goto _start;
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_slice_510_; lean_object* v_nextIt_512_; 
v___x_507_ = lean_string_utf8_next_fast(v_x_477_, v_searcher_491_);
v___x_508_ = lean_nat_sub(v___x_507_, v_searcher_491_);
v___x_509_ = lean_nat_add(v_searcher_491_, v___x_508_);
lean_dec(v___x_508_);
v_slice_510_ = l_String_Slice_subslice_x21(v___x_478_, v_currPos_490_, v_searcher_491_);
lean_inc(v___x_509_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_509_);
lean_ctor_set(v___x_493_, 0, v___x_509_);
v_nextIt_512_ = v___x_493_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_509_);
v_nextIt_512_ = v_reuseFailAlloc_515_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v_startInclusive_513_; lean_object* v_endExclusive_514_; 
v_startInclusive_513_ = lean_ctor_get(v_slice_510_, 0);
lean_inc(v_startInclusive_513_);
v_endExclusive_514_ = lean_ctor_get(v_slice_510_, 1);
lean_inc(v_endExclusive_514_);
lean_dec_ref(v_slice_510_);
v_it_483_ = v_nextIt_512_;
v_startInclusive_484_ = v_startInclusive_513_;
v_endExclusive_485_ = v_endExclusive_514_;
goto v___jp_482_;
}
}
}
else
{
lean_object* v___x_516_; 
lean_del_object(v___x_493_);
lean_dec(v_searcher_491_);
v___x_516_ = lean_box(1);
lean_inc(v___x_479_);
v_it_483_ = v___x_516_;
v_startInclusive_484_ = v_currPos_490_;
v_endExclusive_485_ = v___x_479_;
goto v___jp_482_;
}
}
}
else
{
lean_dec(v___x_479_);
lean_dec_ref(v_x_477_);
return v_b_481_;
}
v___jp_482_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc_ref(v_x_477_);
v___x_486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_486_, 0, v_x_477_);
lean_ctor_set(v___x_486_, 1, v_startInclusive_484_);
lean_ctor_set(v___x_486_, 2, v_endExclusive_485_);
v___x_487_ = l_String_Slice_toString(v___x_486_);
lean_dec_ref(v___x_486_);
v___x_488_ = lean_array_push(v_b_481_, v___x_487_);
v_a_480_ = v_it_483_;
v_b_481_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg___boxed(lean_object* v_x_518_, lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_518_, v___x_519_, v___x_520_, v_a_521_, v_b_522_);
lean_dec_ref(v___x_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object* v_x_528_){
_start:
{
lean_object* v_ss_530_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_SubExpr_Pos_toString___closed__0));
v___x_536_ = lean_string_dec_eq(v_x_528_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_string_utf8_byte_size(v_x_528_);
lean_inc_ref(v_x_528_);
v___x_539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_539_, 0, v_x_528_);
lean_ctor_set(v___x_539_, 1, v___x_537_);
lean_ctor_set(v___x_539_, 2, v___x_538_);
v___x_540_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v___x_539_);
v___x_541_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__1));
v___x_542_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_528_, v___x_539_, v___x_538_, v___x_540_, v___x_541_);
lean_dec_ref(v___x_539_);
v___x_543_ = lean_array_to_list(v___x_542_);
if (lean_obj_tag(v___x_543_) == 1)
{
lean_object* v_head_544_; lean_object* v_tail_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_head_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_head_544_);
v_tail_545_ = lean_ctor_get(v___x_543_, 1);
lean_inc(v_tail_545_);
v___x_546_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__2));
v___x_547_ = lean_string_dec_eq(v_head_544_, v___x_546_);
lean_dec(v_head_544_);
if (v___x_547_ == 0)
{
lean_dec(v_tail_545_);
v_ss_530_ = v___x_543_;
goto v___jp_529_;
}
else
{
lean_object* v___x_548_; size_t v_sz_549_; size_t v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v___x_543_);
v___x_548_ = lean_array_mk(v_tail_545_);
v_sz_549_ = lean_array_size(v___x_548_);
v___x_550_ = ((size_t)0ULL);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_549_, v___x_550_, v___x_548_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_568_; 
v_a_560_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_568_ == 0)
{
v___x_562_ = v___x_551_;
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_551_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_568_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_SubExpr_Pos_ofArray(v_a_560_);
lean_dec(v_a_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
else
{
v_ss_530_ = v___x_543_;
goto v___jp_529_;
}
}
else
{
lean_object* v___x_569_; 
lean_dec_ref(v_x_528_);
v___x_569_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7));
return v___x_569_;
}
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_531_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__0));
v___x_532_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_ss_530_);
lean_dec(v_ss_530_);
v___x_533_ = lean_string_append(v___x_531_, v___x_532_);
lean_dec_ref(v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(lean_object* v_x_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_inst_573_, lean_object* v_R_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_570_, v___x_571_, v___x_572_, v_a_575_, v_b_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___boxed(lean_object* v_x_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_inst_581_, lean_object* v_R_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(v_x_578_, v___x_579_, v___x_580_, v_inst_581_, v_R_582_, v_a_583_, v_b_584_);
lean_dec_ref(v___x_579_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object* v_s_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_SubExpr_Pos_fromString_x3f(v_s_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_591_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x21___closed__0));
v___x_592_ = lean_unsigned_to_nat(142u);
v___x_593_ = lean_unsigned_to_nat(16u);
v___x_594_ = l_mkPanicMessageWithDecl(v___x_590_, v___x_591_, v___x_592_, v___x_593_, v_a_589_);
lean_dec(v_a_589_);
v___x_595_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_588_);
return v_a_596_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEq(lean_object* v_a_599_, lean_object* v_b_600_){
_start:
{
uint8_t v___x_601_; 
v___x_601_ = lean_nat_dec_eq(v_a_599_, v_b_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEq___boxed(lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Lean_SubExpr_Pos_instDecidableEq(v_a_602_, v_b_603_);
lean_dec(v_b_603_);
lean_dec(v_a_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instEmptyCollection(void){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = lean_unsigned_to_nat(1u);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0(lean_object* v_p_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_614_ = ((lean_object*)(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1));
v___x_615_ = l_Lean_SubExpr_Pos_toString(v_p_612_);
v___x_616_ = l_String_quote(v___x_615_);
v___x_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_614_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___boxed(lean_object* v_p_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_SubExpr_Pos_instRepr___lam__0(v_p_619_, v_x_620_);
lean_dec(v_x_620_);
lean_dec(v_p_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJson___lam__0(lean_object* v_s_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v_s_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJson___lam__0(lean_object* v_j_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Json_getStr_x3f(v_j_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_632_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_632_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_641_);
lean_dec_ref(v___x_632_);
v___x_642_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_641_);
return v___x_642_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__2(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_instInhabitedSubExpr_default___closed__1));
v___x_650_ = l_Lean_Expr_const___override(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__3(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__2, &l_Lean_instInhabitedSubExpr_default___closed__2_once, _init_l_Lean_instInhabitedSubExpr_default___closed__2);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default(void){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__3, &l_Lean_instInhabitedSubExpr_default___closed__3_once, _init_l_Lean_instInhabitedSubExpr_default___closed__3);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr(void){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_instInhabitedSubExpr_default;
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* v_e_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v_e_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object* v_s_659_){
_start:
{
lean_object* v_pos_660_; uint8_t v___x_661_; 
v_pos_660_ = lean_ctor_get(v_s_659_, 1);
v___x_661_ = l_Lean_SubExpr_Pos_isRoot(v_pos_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object* v_s_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Lean_SubExpr_isRoot(v_s_662_);
lean_dec_ref(v_s_662_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(lean_object* v_msg_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = l_Lean_instInhabitedSubExpr_default;
v___x_667_ = lean_panic_fn_borrowed(v___x_666_, v_msg_665_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__2(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_671_ = lean_unsigned_to_nat(9u);
v___x_672_ = lean_unsigned_to_nat(181u);
v___x_673_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__0));
v___x_674_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_675_ = l_mkPanicMessageWithDecl(v___x_674_, v___x_673_, v___x_672_, v___x_671_, v___x_670_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object* v_x_676_){
_start:
{
lean_object* v_expr_677_; lean_object* v_pos_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_692_; 
v_expr_677_ = lean_ctor_get(v_x_676_, 0);
v_pos_678_ = lean_ctor_get(v_x_676_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_676_);
if (v_isSharedCheck_692_ == 0)
{
v___x_680_ = v_x_676_;
v_isShared_681_ = v_isSharedCheck_692_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_pos_678_);
lean_inc(v_expr_677_);
lean_dec(v_x_676_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_692_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_b_683_; 
switch(lean_obj_tag(v_expr_677_))
{
case 7:
{
lean_object* v_body_688_; 
v_body_688_ = lean_ctor_get(v_expr_677_, 2);
lean_inc_ref(v_body_688_);
lean_dec_ref(v_expr_677_);
v_b_683_ = v_body_688_;
goto v___jp_682_;
}
case 6:
{
lean_object* v_body_689_; 
v_body_689_ = lean_ctor_get(v_expr_677_, 2);
lean_inc_ref(v_body_689_);
lean_dec_ref(v_expr_677_);
v_b_683_ = v_body_689_;
goto v___jp_682_;
}
default: 
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_del_object(v___x_680_);
lean_dec(v_pos_678_);
lean_dec_ref(v_expr_677_);
v___x_690_ = lean_obj_once(&l_Lean_SubExpr_bindingBody_x21___closed__2, &l_Lean_SubExpr_bindingBody_x21___closed__2_once, _init_l_Lean_SubExpr_bindingBody_x21___closed__2);
v___x_691_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_690_);
return v___x_691_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_684_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_678_);
lean_dec(v_pos_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_684_);
lean_ctor_set(v___x_680_, 0, v_b_683_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_b_683_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_684_);
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
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_695_ = lean_unsigned_to_nat(9u);
v___x_696_ = lean_unsigned_to_nat(186u);
v___x_697_ = ((lean_object*)(l_Lean_SubExpr_bindingDomain_x21___closed__0));
v___x_698_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object* v_x_700_){
_start:
{
lean_object* v_expr_701_; lean_object* v_pos_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_716_; 
v_expr_701_ = lean_ctor_get(v_x_700_, 0);
v_pos_702_ = lean_ctor_get(v_x_700_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_716_ == 0)
{
v___x_704_ = v_x_700_;
v_isShared_705_ = v_isSharedCheck_716_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_pos_702_);
lean_inc(v_expr_701_);
lean_dec(v_x_700_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_716_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_t_707_; 
switch(lean_obj_tag(v_expr_701_))
{
case 7:
{
lean_object* v_binderType_712_; 
v_binderType_712_ = lean_ctor_get(v_expr_701_, 1);
lean_inc_ref(v_binderType_712_);
lean_dec_ref(v_expr_701_);
v_t_707_ = v_binderType_712_;
goto v___jp_706_;
}
case 6:
{
lean_object* v_binderType_713_; 
v_binderType_713_ = lean_ctor_get(v_expr_701_, 1);
lean_inc_ref(v_binderType_713_);
lean_dec_ref(v_expr_701_);
v_t_707_ = v_binderType_713_;
goto v___jp_706_;
}
default: 
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_del_object(v___x_704_);
lean_dec(v_pos_702_);
lean_dec_ref(v_expr_701_);
v___x_714_ = lean_obj_once(&l_Lean_SubExpr_bindingDomain_x21___closed__1, &l_Lean_SubExpr_bindingDomain_x21___closed__1_once, _init_l_Lean_SubExpr_bindingDomain_x21___closed__1);
v___x_715_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_714_);
return v___x_715_;
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_702_);
lean_dec(v_pos_702_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 1, v___x_708_);
lean_ctor_set(v___x_704_, 0, v_t_707_);
v___x_710_ = v___x_704_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_t_707_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId___lam__0(lean_object* v_f_717_){
_start:
{
uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = 1;
v___x_719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_f_717_, v___x_718_);
v___x_720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lam__0(lean_object* v_j_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Name_fromJson_x3f(v_j_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
v_a_734_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_725_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_725_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx(lean_object* v_x_745_){
_start:
{
switch(lean_obj_tag(v_x_745_))
{
case 0:
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(0u);
return v___x_746_;
}
case 1:
{
lean_object* v___x_747_; 
v___x_747_ = lean_unsigned_to_nat(1u);
return v___x_747_;
}
case 2:
{
lean_object* v___x_748_; 
v___x_748_ = lean_unsigned_to_nat(2u);
return v___x_748_;
}
default: 
{
lean_object* v___x_749_; 
v___x_749_ = lean_unsigned_to_nat(3u);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___boxed(lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_SubExpr_GoalLocation_ctorIdx(v_x_750_);
lean_dec_ref(v_x_750_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___redArg(lean_object* v_t_752_, lean_object* v_k_753_){
_start:
{
switch(lean_obj_tag(v_t_752_))
{
case 1:
{
lean_object* v_a_754_; lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_754_ = lean_ctor_get(v_t_752_, 0);
lean_inc(v_a_754_);
v_a_755_ = lean_ctor_get(v_t_752_, 1);
lean_inc(v_a_755_);
lean_dec_ref(v_t_752_);
v___x_756_ = lean_apply_2(v_k_753_, v_a_754_, v_a_755_);
return v___x_756_;
}
case 2:
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v_t_752_, 0);
lean_inc(v_a_757_);
v_a_758_ = lean_ctor_get(v_t_752_, 1);
lean_inc(v_a_758_);
lean_dec_ref(v_t_752_);
v___x_759_ = lean_apply_2(v_k_753_, v_a_757_, v_a_758_);
return v___x_759_;
}
default: 
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_ctor_get(v_t_752_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v_t_752_);
v___x_761_ = lean_apply_1(v_k_753_, v_a_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim(lean_object* v_motive_762_, lean_object* v_ctorIdx_763_, lean_object* v_t_764_, lean_object* v_h_765_, lean_object* v_k_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_764_, v_k_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___boxed(lean_object* v_motive_768_, lean_object* v_ctorIdx_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_SubExpr_GoalLocation_ctorElim(v_motive_768_, v_ctorIdx_769_, v_t_770_, v_h_771_, v_k_772_);
lean_dec(v_ctorIdx_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim___redArg(lean_object* v_t_774_, lean_object* v_hyp_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_774_, v_hyp_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim(lean_object* v_motive_777_, lean_object* v_t_778_, lean_object* v_h_779_, lean_object* v_hyp_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_778_, v_hyp_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim___redArg(lean_object* v_t_782_, lean_object* v_hypType_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_782_, v_hypType_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim(lean_object* v_motive_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_hypType_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_786_, v_hypType_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim___redArg(lean_object* v_t_790_, lean_object* v_hypValue_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_790_, v_hypValue_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim(lean_object* v_motive_793_, lean_object* v_t_794_, lean_object* v_h_795_, lean_object* v_hypValue_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_794_, v_hypValue_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim___redArg(lean_object* v_t_798_, lean_object* v_target_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_798_, v_target_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim(lean_object* v_motive_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_target_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_802_, v_target_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(lean_object* v_json_816_){
_start:
{
lean_object* v___x_817_; 
lean_inc(v_json_816_);
v___x_817_ = l_Lean_Json_getTag_x3f(v_json_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; 
lean_dec(v_json_816_);
v___x_818_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1));
return v___x_818_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_1019_; 
v_val_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_1019_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_1019_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_box(0);
v___x_824_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_825_ = lean_string_dec_eq(v_val_819_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_827_ = lean_string_dec_eq(v_val_819_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
lean_del_object(v___x_821_);
v___x_828_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_829_ = lean_string_dec_eq(v_val_819_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_831_ = lean_string_dec_eq(v_val_819_, v___x_830_);
lean_dec(v_val_819_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_json_816_);
v___x_832_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7));
return v___x_832_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(2u);
v___x_834_ = lean_box(0);
v___x_835_ = l_Lean_Json_parseCtorFields(v_json_816_, v___x_830_, v___x_833_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_a_844_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_835_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_borrowed(v___x_823_, v_a_844_, v___x_845_);
lean_inc(v___x_846_);
v___x_847_ = l_Lean_Name_fromJson_x3f(v___x_846_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_a_844_);
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_856_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_856_);
lean_dec_ref(v___x_847_);
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_array_get(v___x_823_, v_a_844_, v___x_857_);
lean_dec(v_a_844_);
v___x_859_ = l_Lean_Json_getStr_x3f(v___x_858_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_856_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_859_);
v___x_869_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_856_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_886_; 
v_a_878_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_886_ == 0)
{
v___x_880_ = v___x_869_;
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_869_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_886_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_882_, 0, v_a_856_);
lean_ctor_set(v___x_882_, 1, v_a_878_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_882_);
v___x_884_ = v___x_880_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
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
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v_val_819_);
v___x_887_ = lean_unsigned_to_nat(2u);
v___x_888_ = lean_box(0);
v___x_889_ = l_Lean_Json_parseCtorFields(v_json_816_, v___x_828_, v___x_887_, v___x_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_a_898_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_889_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_array_get_borrowed(v___x_823_, v_a_898_, v___x_899_);
lean_inc(v___x_900_);
v___x_901_ = l_Lean_Name_fromJson_x3f(v___x_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_a_898_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_a_910_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_901_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_array_get(v___x_823_, v_a_898_, v___x_911_);
lean_dec(v_a_898_);
v___x_913_ = l_Lean_Json_getStr_x3f(v___x_912_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_a_910_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_923_; 
v_a_922_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_922_);
lean_dec_ref(v___x_913_);
v___x_923_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_a_910_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_a_932_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v___x_923_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_923_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_936_, 0, v_a_910_);
lean_ctor_set(v___x_936_, 1, v_a_932_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
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
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_val_819_);
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_box(0);
v___x_943_ = l_Lean_Json_parseCtorFields(v_json_816_, v___x_826_, v___x_941_, v___x_942_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_del_object(v___x_821_);
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_a_952_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_952_);
lean_dec_ref(v___x_943_);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_array_get(v___x_823_, v_a_952_, v___x_953_);
lean_dec(v_a_952_);
v___x_955_ = l_Lean_Name_fromJson_x3f(v___x_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_821_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_974_; 
v_a_964_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_966_ = v___x_955_;
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_955_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v_a_964_);
v___x_969_ = v___x_821_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_973_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_971_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
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
}
}
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec(v_val_819_);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = lean_box(0);
v___x_977_ = l_Lean_Json_parseCtorFields(v_json_816_, v___x_824_, v___x_975_, v___x_976_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_del_object(v___x_821_);
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_986_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_986_);
lean_dec_ref(v___x_977_);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_array_get(v___x_823_, v_a_986_, v___x_987_);
lean_dec(v_a_986_);
v___x_989_ = l_Lean_Json_getStr_x3f(v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_del_object(v___x_821_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_999_; 
v_a_998_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_998_);
lean_dec_ref(v___x_989_);
v___x_999_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_998_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
lean_del_object(v___x_821_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1018_; 
v_a_1008_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1010_ = v___x_999_;
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_999_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 3);
lean_ctor_set(v___x_821_, 0, v_a_1008_);
v___x_1013_ = v___x_821_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
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
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalLocation_toJson(lean_object* v_x_1022_){
_start:
{
switch(lean_obj_tag(v_x_1022_))
{
case 0:
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1037_; 
v_a_1023_ = lean_ctor_get(v_x_1022_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1025_ = v_x_1022_;
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v_x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1037_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
v___x_1027_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_1028_ = 1;
v___x_1029_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1023_, v___x_1028_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 3);
lean_ctor_set(v___x_1025_, 0, v___x_1029_);
v___x_1031_ = v___x_1025_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1027_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_Json_mkObj(v___x_1034_);
return v___x_1035_;
}
}
}
case 1:
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1060_; 
v_a_1038_ = lean_ctor_get(v_x_1022_, 0);
v_a_1039_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1041_ = v_x_1022_;
v_isShared_1042_ = v_isSharedCheck_1060_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_inc(v_a_1038_);
lean_dec(v_x_1022_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1060_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1043_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_1044_ = 1;
v___x_1045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1038_, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
v___x_1047_ = l_Lean_SubExpr_Pos_toString(v_a_1039_);
lean_dec(v_a_1039_);
v___x_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(2u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1046_);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_1048_);
v___x_1053_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 0);
lean_ctor_set(v___x_1041_, 1, v___x_1053_);
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1055_ = v___x_1041_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_Json_mkObj(v___x_1057_);
return v___x_1058_;
}
}
}
case 2:
{
lean_object* v_a_1061_; lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1083_; 
v_a_1061_ = lean_ctor_get(v_x_1022_, 0);
v_a_1062_ = lean_ctor_get(v_x_1022_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1064_ = v_x_1022_;
v_isShared_1065_ = v_isSharedCheck_1083_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_inc(v_a_1061_);
lean_dec(v_x_1022_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1083_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1066_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_1067_ = 1;
v___x_1068_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1061_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
v___x_1070_ = l_Lean_SubExpr_Pos_toString(v_a_1062_);
lean_dec(v_a_1062_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = lean_unsigned_to_nat(2u);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1072_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1069_);
v___x_1075_ = lean_array_push(v___x_1074_, v___x_1071_);
v___x_1076_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 0);
lean_ctor_set(v___x_1064_, 1, v___x_1076_);
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1078_ = v___x_1064_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = l_Lean_Json_mkObj(v___x_1080_);
return v___x_1081_;
}
}
}
default: 
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1097_; 
v_a_1084_ = lean_ctor_get(v_x_1022_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1022_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1086_ = v_x_1022_;
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v_x_1022_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1097_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_1089_ = l_Lean_SubExpr_Pos_toString(v_a_1084_);
lean_dec(v_a_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1088_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_Json_mkObj(v___x_1094_);
return v___x_1095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(lean_object* v_j_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = l_Lean_Json_getObjValD(v_j_1100_, v_k_1101_);
v___x_1103_ = l_Lean_Name_fromJson_x3f(v___x_1102_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1103_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1103_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0___boxed(lean_object* v_j_1120_, lean_object* v_k_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_j_1120_, v_k_1121_);
lean_dec_ref(v_k_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(lean_object* v_j_1123_, lean_object* v_k_1124_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = l_Lean_Json_getObjValD(v_j_1123_, v_k_1124_);
v___x_1126_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1___boxed(lean_object* v_j_1127_, lean_object* v_k_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_j_1127_, v_k_1128_);
lean_dec_ref(v_k_1128_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = 1;
v___x_1139_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4));
v___x_1140_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6));
v___x_1143_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5);
v___x_1144_ = lean_string_append(v___x_1143_, v___x_1142_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1147_ = 1;
v___x_1148_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8));
v___x_1149_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1148_, v___x_1147_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1150_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9);
v___x_1151_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1152_ = lean_string_append(v___x_1151_, v___x_1150_);
return v___x_1152_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1155_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10);
v___x_1156_ = lean_string_append(v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = 1;
v___x_1161_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14));
v___x_1162_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1161_, v___x_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15);
v___x_1164_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1165_ = lean_string_append(v___x_1164_, v___x_1163_);
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1167_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16);
v___x_1168_ = lean_string_append(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson(lean_object* v_json_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
lean_inc(v_json_1169_);
v___x_1171_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_json_1169_, v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1181_; 
lean_dec(v_json_1169_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1181_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12);
v___x_1177_ = lean_string_append(v___x_1176_, v_a_1172_);
lean_dec(v_a_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
else
{
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec(v_json_1169_);
v_a_1182_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1171_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1171_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set_tag(v___x_1184_, 0);
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1171_);
v___x_1191_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1192_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_json_1169_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1202_; 
lean_dec(v_a_1190_);
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1202_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1197_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17);
v___x_1198_ = lean_string_append(v___x_1197_, v_a_1193_);
lean_dec(v_a_1193_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1198_);
v___x_1200_ = v___x_1195_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
else
{
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec(v_a_1190_);
v_a_1203_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1192_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1192_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 0);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1211_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1192_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1192_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_a_1190_);
lean_ctor_set(v___x_1215_, 1, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
if (lean_obj_tag(v_a_1222_) == 0)
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_array_to_list(v_a_1223_);
return v___x_1224_;
}
else
{
lean_object* v_head_1225_; lean_object* v_tail_1226_; lean_object* v___x_1227_; 
v_head_1225_ = lean_ctor_get(v_a_1222_, 0);
lean_inc(v_head_1225_);
v_tail_1226_ = lean_ctor_get(v_a_1222_, 1);
lean_inc(v_tail_1226_);
lean_dec_ref(v_a_1222_);
v___x_1227_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1223_, v_head_1225_);
v_a_1222_ = v_tail_1226_;
v_a_1223_ = v___x_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalsLocation_toJson(lean_object* v_x_1231_){
_start:
{
lean_object* v_mvarId_1232_; lean_object* v_loc_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1255_; 
v_mvarId_1232_ = lean_ctor_get(v_x_1231_, 0);
v_loc_1233_ = lean_ctor_get(v_x_1231_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_x_1231_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1235_ = v_x_1231_;
v_isShared_1236_ = v_isSharedCheck_1255_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_loc_1233_);
lean_inc(v_mvarId_1232_);
lean_dec(v_x_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1255_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1237_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
v___x_1238_ = 1;
v___x_1239_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1232_, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 1, v___x_1240_);
lean_ctor_set(v___x_1235_, 0, v___x_1237_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1246_ = l_Lean_SubExpr_instToJsonGoalLocation_toJson(v_loc_1233_);
v___x_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v___x_1243_);
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1243_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1244_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0));
v___x_1252_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(v___x_1250_, v___x_1251_);
v___x_1253_ = l_Lean_Json_mkObj(v___x_1252_);
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0(lean_object* v_p_1258_, lean_object* v_visit_1259_, lean_object* v_arg_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_1258_);
v___x_1263_ = lean_apply_2(v_visit_1259_, v___x_1262_, v_arg_1260_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed(lean_object* v_p_1264_, lean_object* v_visit_1265_, lean_object* v_arg_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Expr_traverseAppWithPos___redArg___lam__0(v_p_1264_, v_visit_1265_, v_arg_1266_, v_x_1267_);
lean_dec(v_p_1264_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object* v_inst_1269_, lean_object* v_visit_1270_, lean_object* v_p_1271_, lean_object* v_e_1272_){
_start:
{
if (lean_obj_tag(v_e_1272_) == 5)
{
lean_object* v_toApplicative_1273_; lean_object* v_toFunctor_1274_; lean_object* v_toSeq_1275_; lean_object* v_fn_1276_; lean_object* v_arg_1277_; lean_object* v_map_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_toApplicative_1273_ = lean_ctor_get(v_inst_1269_, 0);
v_toFunctor_1274_ = lean_ctor_get(v_toApplicative_1273_, 0);
v_toSeq_1275_ = lean_ctor_get(v_toApplicative_1273_, 2);
lean_inc(v_toSeq_1275_);
v_fn_1276_ = lean_ctor_get(v_e_1272_, 0);
lean_inc_ref(v_fn_1276_);
v_arg_1277_ = lean_ctor_get(v_e_1272_, 1);
v_map_1278_ = lean_ctor_get(v_toFunctor_1274_, 0);
lean_inc(v_map_1278_);
lean_inc_ref(v_arg_1277_);
lean_inc(v_visit_1270_);
lean_inc(v_p_1271_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1279_, 0, v_p_1271_);
lean_closure_set(v___f_1279_, 1, v_visit_1270_);
lean_closure_set(v___f_1279_, 2, v_arg_1277_);
v___x_1280_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_1280_, 0, v_e_1272_);
v___x_1281_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_1271_);
lean_dec(v_p_1271_);
v___x_1282_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1269_, v_visit_1270_, v___x_1281_, v_fn_1276_);
v___x_1283_ = lean_apply_4(v_map_1278_, lean_box(0), lean_box(0), v___x_1280_, v___x_1282_);
v___x_1284_ = lean_apply_4(v_toSeq_1275_, lean_box(0), lean_box(0), v___x_1283_, v___f_1279_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; 
lean_dec_ref(v_inst_1269_);
v___x_1285_ = lean_apply_2(v_visit_1270_, v_p_1271_, v_e_1272_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object* v_M_1286_, lean_object* v_inst_1287_, lean_object* v_visit_1288_, lean_object* v_p_1289_, lean_object* v_e_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1287_, v_visit_1288_, v_p_1289_, v_e_1290_);
return v___x_1291_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_SubExpr_Pos_maxChildren = _init_l_Lean_SubExpr_Pos_maxChildren();
lean_mark_persistent(l_Lean_SubExpr_Pos_maxChildren);
l_Lean_SubExpr_Pos_typeCoord = _init_l_Lean_SubExpr_Pos_typeCoord();
lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord);
l_Lean_SubExpr_Pos_root = _init_l_Lean_SubExpr_Pos_root();
lean_mark_persistent(l_Lean_SubExpr_Pos_root);
l_Lean_SubExpr_Pos_instInhabited = _init_l_Lean_SubExpr_Pos_instInhabited();
lean_mark_persistent(l_Lean_SubExpr_Pos_instInhabited);
l_Lean_SubExpr_Pos_instEmptyCollection = _init_l_Lean_SubExpr_Pos_instEmptyCollection();
lean_mark_persistent(l_Lean_SubExpr_Pos_instEmptyCollection);
l_Lean_instInhabitedSubExpr_default = _init_l_Lean_instInhabitedSubExpr_default();
lean_mark_persistent(l_Lean_instInhabitedSubExpr_default);
l_Lean_instInhabitedSubExpr = _init_l_Lean_instInhabitedSubExpr();
lean_mark_persistent(l_Lean_instInhabitedSubExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_SubExpr(builtin);
}
#ifdef __cplusplus
}
#endif
