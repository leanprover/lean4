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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0;
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
lean_object* v_toApplicative_122_; lean_object* v_toBind_123_; lean_object* v_toPure_124_; uint8_t v___x_125_; 
v_toApplicative_122_ = lean_ctor_get(v_inst_118_, 0);
v_toBind_123_ = lean_ctor_get(v_inst_118_, 1);
lean_inc(v_toBind_123_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_122_, 1);
v___x_125_ = l_Lean_SubExpr_Pos_isRoot(v_p_121_);
if (v___x_125_ == 0)
{
lean_object* v___f_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc(v_f_119_);
lean_inc(v_p_121_);
v___f_126_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_126_, 0, v_p_121_);
lean_closure_set(v___f_126_, 1, v_f_119_);
v___x_127_ = l_Lean_SubExpr_Pos_tail(v_p_121_);
lean_dec(v_p_121_);
v___x_128_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_118_, v_f_119_, v_init_120_, v___x_127_);
v___x_129_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_128_, v___f_126_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_inc(v_toPure_124_);
lean_dec(v_toBind_123_);
lean_dec(v_p_121_);
lean_dec(v_f_119_);
lean_dec_ref(v_inst_118_);
v___x_130_ = lean_apply_2(v_toPure_124_, lean_box(0), v_init_120_);
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
lean_object* v_toApplicative_156_; lean_object* v_toBind_157_; lean_object* v_toPure_158_; uint8_t v___x_159_; 
v_toApplicative_156_ = lean_ctor_get(v_inst_152_, 0);
v_toBind_157_ = lean_ctor_get(v_inst_152_, 1);
lean_inc(v_toBind_157_);
v_toPure_158_ = lean_ctor_get(v_toApplicative_156_, 1);
v___x_159_ = l_Lean_SubExpr_Pos_isRoot(v_p_154_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = l_Lean_SubExpr_Pos_head(v_p_154_);
lean_inc(v_f_153_);
v___x_161_ = lean_apply_2(v_f_153_, v___x_160_, v_init_155_);
v___x_162_ = l_Lean_SubExpr_Pos_tail(v_p_154_);
v___x_163_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___redArg___boxed), 4, 3);
lean_closure_set(v___x_163_, 0, v_inst_152_);
lean_closure_set(v___x_163_, 1, v_f_153_);
lean_closure_set(v___x_163_, 2, v___x_162_);
v___x_164_ = lean_apply_4(v_toBind_157_, lean_box(0), lean_box(0), v___x_161_, v___x_163_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; 
lean_inc(v_toPure_158_);
lean_dec(v_toBind_157_);
lean_dec(v_f_153_);
lean_dec_ref(v_inst_152_);
v___x_165_ = lean_apply_2(v_toPure_158_, lean_box(0), v_init_155_);
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
lean_dec_ref_known(v___x_204_, 1);
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
lean_dec_ref_known(v___x_213_, 1);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg(){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___closed__0));
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___boxed(lean_object* v___dummy_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
return v_res_417_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(lean_object* v_s_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___boxed(lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v_s_421_);
lean_dec_ref(v_s_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(size_t v_sz_423_, size_t v_i_424_, lean_object* v_bs_425_){
_start:
{
uint8_t v___x_426_; 
v___x_426_ = lean_usize_dec_lt(v_i_424_, v_sz_423_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_bs_425_);
return v___x_427_;
}
else
{
lean_object* v_v_428_; lean_object* v___x_429_; 
v_v_428_ = lean_array_uget_borrowed(v_bs_425_, v_i_424_);
v___x_429_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_v_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec_ref(v_bs_425_);
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_439_; lean_object* v_bs_x27_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v_a_438_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_429_, 1);
v___x_439_ = lean_unsigned_to_nat(0u);
v_bs_x27_440_ = lean_array_uset(v_bs_425_, v_i_424_, v___x_439_);
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_add(v_i_424_, v___x_441_);
v___x_443_ = lean_array_uset(v_bs_x27_440_, v_i_424_, v_a_438_);
v_i_424_ = v___x_442_;
v_bs_425_ = v___x_443_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3___boxed(lean_object* v_sz_445_, lean_object* v_i_446_, lean_object* v_bs_447_){
_start:
{
size_t v_sz_boxed_448_; size_t v_i_boxed_449_; lean_object* v_res_450_; 
v_sz_boxed_448_ = lean_unbox_usize(v_sz_445_);
lean_dec(v_sz_445_);
v_i_boxed_449_ = lean_unbox_usize(v_i_446_);
lean_dec(v_i_446_);
v_res_450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_boxed_448_, v_i_boxed_449_, v_bs_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
return v_x_452_;
}
else
{
lean_object* v_head_454_; lean_object* v_tail_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_head_454_ = lean_ctor_get(v_x_453_, 0);
v_tail_455_ = lean_ctor_get(v_x_453_, 1);
v___x_456_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0));
v___x_457_ = lean_string_append(v_x_452_, v___x_456_);
v___x_458_ = lean_string_append(v___x_457_, v_head_454_);
v_x_452_ = v___x_458_;
v_x_453_ = v_tail_455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0));
return v___x_467_;
}
else
{
lean_object* v_tail_468_; 
v_tail_468_ = lean_ctor_get(v_x_466_, 1);
if (lean_obj_tag(v_tail_468_) == 0)
{
lean_object* v_head_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_head_469_ = lean_ctor_get(v_x_466_, 0);
v___x_470_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_471_ = lean_string_append(v___x_470_, v_head_469_);
v___x_472_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
return v___x_473_;
}
else
{
lean_object* v_head_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint32_t v___x_478_; lean_object* v___x_479_; 
v_head_474_ = lean_ctor_get(v_x_466_, 0);
v___x_475_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_476_ = lean_string_append(v___x_475_, v_head_474_);
v___x_477_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v___x_476_, v_tail_468_);
v___x_478_ = 93;
v___x_479_ = lean_string_push(v___x_477_, v___x_478_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___boxed(lean_object* v_x_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_x_480_);
lean_dec(v_x_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(lean_object* v_x_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v_it_488_; lean_object* v_startInclusive_489_; lean_object* v_endExclusive_490_; 
if (lean_obj_tag(v_a_485_) == 0)
{
lean_object* v_currPos_495_; lean_object* v_searcher_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_519_; 
v_currPos_495_ = lean_ctor_get(v_a_485_, 0);
v_searcher_496_ = lean_ctor_get(v_a_485_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_519_ == 0)
{
v___x_498_ = v_a_485_;
v_isShared_499_ = v_isSharedCheck_519_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_searcher_496_);
lean_inc(v_currPos_495_);
lean_dec(v_a_485_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_519_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
uint8_t v_decide_500_; 
v_decide_500_ = lean_nat_dec_eq(v_searcher_496_, v___x_484_);
if (v_decide_500_ == 0)
{
uint32_t v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
v___x_501_ = 47;
v___x_502_ = lean_string_utf8_get_fast(v_x_482_, v_searcher_496_);
v___x_503_ = lean_uint32_dec_eq(v___x_502_, v___x_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_string_utf8_next_fast(v_x_482_, v_searcher_496_);
lean_dec(v_searcher_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_504_);
v___x_506_ = v___x_498_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_currPos_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_508_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_485_ = v___x_506_;
goto _start;
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_slice_512_; lean_object* v_nextIt_514_; 
v___x_509_ = lean_string_utf8_next_fast(v_x_482_, v_searcher_496_);
v___x_510_ = lean_nat_sub(v___x_509_, v_searcher_496_);
v___x_511_ = lean_nat_add(v_searcher_496_, v___x_510_);
lean_dec(v___x_510_);
v_slice_512_ = l_String_Slice_subslice_x21(v___x_483_, v_currPos_495_, v_searcher_496_);
lean_inc(v___x_511_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 1, v___x_511_);
lean_ctor_set(v___x_498_, 0, v___x_511_);
v_nextIt_514_ = v___x_498_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_511_);
v_nextIt_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v_startInclusive_515_; lean_object* v_endExclusive_516_; 
v_startInclusive_515_ = lean_ctor_get(v_slice_512_, 0);
lean_inc(v_startInclusive_515_);
v_endExclusive_516_ = lean_ctor_get(v_slice_512_, 1);
lean_inc(v_endExclusive_516_);
lean_dec_ref(v_slice_512_);
v_it_488_ = v_nextIt_514_;
v_startInclusive_489_ = v_startInclusive_515_;
v_endExclusive_490_ = v_endExclusive_516_;
goto v___jp_487_;
}
}
}
else
{
lean_object* v___x_518_; 
lean_del_object(v___x_498_);
lean_dec(v_searcher_496_);
v___x_518_ = lean_box(1);
lean_inc(v___x_484_);
v_it_488_ = v___x_518_;
v_startInclusive_489_ = v_currPos_495_;
v_endExclusive_490_ = v___x_484_;
goto v___jp_487_;
}
}
}
else
{
lean_dec(v___x_484_);
lean_dec_ref(v_x_482_);
return v_b_486_;
}
v___jp_487_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc_ref(v_x_482_);
v___x_491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_491_, 0, v_x_482_);
lean_ctor_set(v___x_491_, 1, v_startInclusive_489_);
lean_ctor_set(v___x_491_, 2, v_endExclusive_490_);
v___x_492_ = l_String_Slice_toString(v___x_491_);
lean_dec_ref_known(v___x_491_, 3);
v___x_493_ = lean_array_push(v_b_486_, v___x_492_);
v_a_485_ = v_it_488_;
v_b_486_ = v___x_493_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg___boxed(lean_object* v_x_520_, lean_object* v___x_521_, lean_object* v___x_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_520_, v___x_521_, v___x_522_, v_a_523_, v_b_524_);
lean_dec_ref(v___x_521_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object* v_x_530_){
_start:
{
lean_object* v_ss_532_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_SubExpr_Pos_toString___closed__0));
v___x_538_ = lean_string_dec_eq(v_x_530_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_string_utf8_byte_size(v_x_530_);
lean_inc_ref(v_x_530_);
v___x_541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_541_, 0, v_x_530_);
lean_ctor_set(v___x_541_, 1, v___x_539_);
lean_ctor_set(v___x_541_, 2, v___x_540_);
v___x_542_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0);
v___x_543_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__1));
v___x_544_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_530_, v___x_541_, v___x_540_, v___x_542_, v___x_543_);
lean_dec_ref_known(v___x_541_, 3);
v___x_545_ = lean_array_to_list(v___x_544_);
if (lean_obj_tag(v___x_545_) == 1)
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_head_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_head_546_);
v_tail_547_ = lean_ctor_get(v___x_545_, 1);
lean_inc(v_tail_547_);
v___x_548_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__2));
v___x_549_ = lean_string_dec_eq(v_head_546_, v___x_548_);
lean_dec(v_head_546_);
if (v___x_549_ == 0)
{
lean_dec(v_tail_547_);
v_ss_532_ = v___x_545_;
goto v___jp_531_;
}
else
{
lean_object* v___x_550_; size_t v_sz_551_; size_t v___x_552_; lean_object* v___x_553_; 
lean_dec_ref_known(v___x_545_, 2);
v___x_550_ = lean_array_mk(v_tail_547_);
v_sz_551_ = lean_array_size(v___x_550_);
v___x_552_ = ((size_t)0ULL);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_551_, v___x_552_, v___x_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_a_562_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v___x_553_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_553_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_Lean_SubExpr_Pos_ofArray(v_a_562_);
lean_dec(v_a_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
else
{
v_ss_532_ = v___x_545_;
goto v___jp_531_;
}
}
else
{
lean_object* v___x_571_; 
lean_dec_ref(v_x_530_);
v___x_571_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7));
return v___x_571_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__0));
v___x_534_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_ss_532_);
lean_dec(v_ss_532_);
v___x_535_ = lean_string_append(v___x_533_, v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(lean_object* v_x_572_, lean_object* v___x_573_, lean_object* v___x_574_, lean_object* v_inst_575_, lean_object* v_R_576_, lean_object* v_a_577_, lean_object* v_b_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_572_, v___x_573_, v___x_574_, v_a_577_, v_b_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___boxed(lean_object* v_x_580_, lean_object* v___x_581_, lean_object* v___x_582_, lean_object* v_inst_583_, lean_object* v_R_584_, lean_object* v_a_585_, lean_object* v_b_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(v_x_580_, v___x_581_, v___x_582_, v_inst_583_, v_R_584_, v_a_585_, v_b_586_);
lean_dec_ref(v___x_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object* v_s_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_SubExpr_Pos_fromString_x3f(v_s_589_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_593_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x21___closed__0));
v___x_594_ = lean_unsigned_to_nat(140u);
v___x_595_ = lean_unsigned_to_nat(16u);
v___x_596_ = l_mkPanicMessageWithDecl(v___x_592_, v___x_593_, v___x_594_, v___x_595_, v_a_591_);
lean_dec(v_a_591_);
v___x_597_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_596_);
return v___x_597_;
}
else
{
lean_object* v_a_598_; 
v_a_598_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_590_, 1);
return v_a_598_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_Pos_instDecidableEq(lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_nat_dec_eq(v_a_601_, v_b_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEq___boxed(lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Lean_SubExpr_Pos_instDecidableEq(v_a_604_, v_b_605_);
lean_dec(v_b_605_);
lean_dec(v_a_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instEmptyCollection(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = lean_unsigned_to_nat(1u);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0(lean_object* v_p_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_616_ = ((lean_object*)(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1));
v___x_617_ = l_Lean_SubExpr_Pos_toString(v_p_614_);
v___x_618_ = l_String_quote(v___x_617_);
v___x_619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
v___x_620_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_616_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___boxed(lean_object* v_p_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_SubExpr_Pos_instRepr___lam__0(v_p_621_, v_x_622_);
lean_dec(v_x_622_);
lean_dec(v_p_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJson___lam__0(lean_object* v_s_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_627_, 0, v_s_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJson___lam__0(lean_object* v_j_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Json_getStr_x3f(v_j_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_634_, 1);
v___x_644_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_643_);
return v___x_644_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__2(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_box(0);
v___x_651_ = ((lean_object*)(l_Lean_instInhabitedSubExpr_default___closed__1));
v___x_652_ = l_Lean_Expr_const___override(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__2, &l_Lean_instInhabitedSubExpr_default___closed__2_once, _init_l_Lean_instInhabitedSubExpr_default___closed__2);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__3, &l_Lean_instInhabitedSubExpr_default___closed__3_once, _init_l_Lean_instInhabitedSubExpr_default___closed__3);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_instInhabitedSubExpr_default;
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* v_e_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_660_, 0, v_e_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT uint8_t l_Lean_SubExpr_isRoot(lean_object* v_s_661_){
_start:
{
lean_object* v_pos_662_; uint8_t v___x_663_; 
v_pos_662_ = lean_ctor_get(v_s_661_, 1);
v___x_663_ = l_Lean_SubExpr_Pos_isRoot(v_pos_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object* v_s_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Lean_SubExpr_isRoot(v_s_664_);
lean_dec_ref(v_s_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(lean_object* v_msg_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = l_Lean_instInhabitedSubExpr_default;
v___x_669_ = lean_panic_fn_borrowed(v___x_668_, v_msg_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__2(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_673_ = lean_unsigned_to_nat(9u);
v___x_674_ = lean_unsigned_to_nat(179u);
v___x_675_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__0));
v___x_676_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_677_ = l_mkPanicMessageWithDecl(v___x_676_, v___x_675_, v___x_674_, v___x_673_, v___x_672_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object* v_x_678_){
_start:
{
lean_object* v_expr_679_; lean_object* v_pos_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_694_; 
v_expr_679_ = lean_ctor_get(v_x_678_, 0);
v_pos_680_ = lean_ctor_get(v_x_678_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_694_ == 0)
{
v___x_682_ = v_x_678_;
v_isShared_683_ = v_isSharedCheck_694_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_pos_680_);
lean_inc(v_expr_679_);
lean_dec(v_x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_694_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_b_685_; 
switch(lean_obj_tag(v_expr_679_))
{
case 7:
{
lean_object* v_body_690_; 
v_body_690_ = lean_ctor_get(v_expr_679_, 2);
lean_inc_ref(v_body_690_);
lean_dec_ref_known(v_expr_679_, 3);
v_b_685_ = v_body_690_;
goto v___jp_684_;
}
case 6:
{
lean_object* v_body_691_; 
v_body_691_ = lean_ctor_get(v_expr_679_, 2);
lean_inc_ref(v_body_691_);
lean_dec_ref_known(v_expr_679_, 3);
v_b_685_ = v_body_691_;
goto v___jp_684_;
}
default: 
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_del_object(v___x_682_);
lean_dec(v_pos_680_);
lean_dec_ref(v_expr_679_);
v___x_692_ = lean_obj_once(&l_Lean_SubExpr_bindingBody_x21___closed__2, &l_Lean_SubExpr_bindingBody_x21___closed__2_once, _init_l_Lean_SubExpr_bindingBody_x21___closed__2);
v___x_693_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_692_);
return v___x_693_;
}
}
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_680_);
lean_dec(v_pos_680_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_686_);
lean_ctor_set(v___x_682_, 0, v_b_685_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_b_685_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_696_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_697_ = lean_unsigned_to_nat(9u);
v___x_698_ = lean_unsigned_to_nat(184u);
v___x_699_ = ((lean_object*)(l_Lean_SubExpr_bindingDomain_x21___closed__0));
v___x_700_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_701_ = l_mkPanicMessageWithDecl(v___x_700_, v___x_699_, v___x_698_, v___x_697_, v___x_696_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object* v_x_702_){
_start:
{
lean_object* v_expr_703_; lean_object* v_pos_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_718_; 
v_expr_703_ = lean_ctor_get(v_x_702_, 0);
v_pos_704_ = lean_ctor_get(v_x_702_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_702_);
if (v_isSharedCheck_718_ == 0)
{
v___x_706_ = v_x_702_;
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_pos_704_);
lean_inc(v_expr_703_);
lean_dec(v_x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_718_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_t_709_; 
switch(lean_obj_tag(v_expr_703_))
{
case 7:
{
lean_object* v_binderType_714_; 
v_binderType_714_ = lean_ctor_get(v_expr_703_, 1);
lean_inc_ref(v_binderType_714_);
lean_dec_ref_known(v_expr_703_, 3);
v_t_709_ = v_binderType_714_;
goto v___jp_708_;
}
case 6:
{
lean_object* v_binderType_715_; 
v_binderType_715_ = lean_ctor_get(v_expr_703_, 1);
lean_inc_ref(v_binderType_715_);
lean_dec_ref_known(v_expr_703_, 3);
v_t_709_ = v_binderType_715_;
goto v___jp_708_;
}
default: 
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_del_object(v___x_706_);
lean_dec(v_pos_704_);
lean_dec_ref(v_expr_703_);
v___x_716_ = lean_obj_once(&l_Lean_SubExpr_bindingDomain_x21___closed__1, &l_Lean_SubExpr_bindingDomain_x21___closed__1_once, _init_l_Lean_SubExpr_bindingDomain_x21___closed__1);
v___x_717_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_716_);
return v___x_717_;
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_704_);
lean_dec(v_pos_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 1, v___x_710_);
lean_ctor_set(v___x_706_, 0, v_t_709_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_t_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId___lam__0(lean_object* v_f_719_){
_start:
{
uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = 1;
v___x_721_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_f_719_, v___x_720_);
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lam__0(lean_object* v_j_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Name_fromJson_x3f(v_j_726_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_727_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_727_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx(lean_object* v_x_747_){
_start:
{
switch(lean_obj_tag(v_x_747_))
{
case 0:
{
lean_object* v___x_748_; 
v___x_748_ = lean_unsigned_to_nat(0u);
return v___x_748_;
}
case 1:
{
lean_object* v___x_749_; 
v___x_749_ = lean_unsigned_to_nat(1u);
return v___x_749_;
}
case 2:
{
lean_object* v___x_750_; 
v___x_750_ = lean_unsigned_to_nat(2u);
return v___x_750_;
}
default: 
{
lean_object* v___x_751_; 
v___x_751_ = lean_unsigned_to_nat(3u);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___boxed(lean_object* v_x_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_SubExpr_GoalLocation_ctorIdx(v_x_752_);
lean_dec_ref(v_x_752_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___redArg(lean_object* v_t_754_, lean_object* v_k_755_){
_start:
{
switch(lean_obj_tag(v_t_754_))
{
case 1:
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v_t_754_, 0);
lean_inc(v_a_756_);
v_a_757_ = lean_ctor_get(v_t_754_, 1);
lean_inc(v_a_757_);
lean_dec_ref_known(v_t_754_, 2);
v___x_758_ = lean_apply_2(v_k_755_, v_a_756_, v_a_757_);
return v___x_758_;
}
case 2:
{
lean_object* v_a_759_; lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v_t_754_, 0);
lean_inc(v_a_759_);
v_a_760_ = lean_ctor_get(v_t_754_, 1);
lean_inc(v_a_760_);
lean_dec_ref_known(v_t_754_, 2);
v___x_761_ = lean_apply_2(v_k_755_, v_a_759_, v_a_760_);
return v___x_761_;
}
default: 
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v_t_754_, 0);
lean_inc(v_a_762_);
lean_dec_ref(v_t_754_);
v___x_763_ = lean_apply_1(v_k_755_, v_a_762_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim(lean_object* v_motive_764_, lean_object* v_ctorIdx_765_, lean_object* v_t_766_, lean_object* v_h_767_, lean_object* v_k_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_766_, v_k_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___boxed(lean_object* v_motive_770_, lean_object* v_ctorIdx_771_, lean_object* v_t_772_, lean_object* v_h_773_, lean_object* v_k_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_SubExpr_GoalLocation_ctorElim(v_motive_770_, v_ctorIdx_771_, v_t_772_, v_h_773_, v_k_774_);
lean_dec(v_ctorIdx_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim___redArg(lean_object* v_t_776_, lean_object* v_hyp_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_776_, v_hyp_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim(lean_object* v_motive_779_, lean_object* v_t_780_, lean_object* v_h_781_, lean_object* v_hyp_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_780_, v_hyp_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim___redArg(lean_object* v_t_784_, lean_object* v_hypType_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_784_, v_hypType_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim(lean_object* v_motive_787_, lean_object* v_t_788_, lean_object* v_h_789_, lean_object* v_hypType_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_788_, v_hypType_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim___redArg(lean_object* v_t_792_, lean_object* v_hypValue_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_792_, v_hypValue_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim(lean_object* v_motive_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_hypValue_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_796_, v_hypValue_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim___redArg(lean_object* v_t_800_, lean_object* v_target_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_800_, v_target_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim(lean_object* v_motive_803_, lean_object* v_t_804_, lean_object* v_h_805_, lean_object* v_target_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_804_, v_target_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(lean_object* v_json_818_){
_start:
{
lean_object* v___x_819_; 
lean_inc(v_json_818_);
v___x_819_ = l_Lean_Json_getTag_x3f(v_json_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v___x_820_; 
lean_dec(v_json_818_);
v___x_820_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1));
return v___x_820_;
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_1021_; 
v_val_821_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_1021_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_1021_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_box(0);
v___x_826_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_827_ = lean_string_dec_eq(v_val_821_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_829_ = lean_string_dec_eq(v_val_821_, v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; uint8_t v___x_831_; 
lean_del_object(v___x_823_);
v___x_830_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_831_ = lean_string_dec_eq(v_val_821_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_833_ = lean_string_dec_eq(v_val_821_, v___x_832_);
lean_dec(v_val_821_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v_json_818_);
v___x_834_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7));
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(2u);
v___x_836_ = lean_box(0);
v___x_837_ = l_Lean_Json_parseCtorFields(v_json_818_, v___x_832_, v___x_835_, v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_845_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_845_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_845_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_843_; 
if (v_isShared_841_ == 0)
{
v___x_843_ = v___x_840_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_a_846_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_837_, 1);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_array_get_borrowed(v___x_825_, v_a_846_, v___x_847_);
lean_inc(v___x_848_);
v___x_849_ = l_Lean_Name_fromJson_x3f(v___x_848_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_846_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_858_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_849_, 1);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_array_get(v___x_825_, v_a_846_, v___x_859_);
lean_dec(v_a_846_);
v___x_861_ = l_Lean_Json_getStr_x3f(v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_858_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_871_; 
v_a_870_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_861_, 1);
v___x_871_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_858_);
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_a_880_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v___x_871_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_871_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_884_, 0, v_a_858_);
lean_ctor_set(v___x_884_, 1, v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
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
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_val_821_);
v___x_889_ = lean_unsigned_to_nat(2u);
v___x_890_ = lean_box(0);
v___x_891_ = l_Lean_Json_parseCtorFields(v_json_818_, v___x_830_, v___x_889_, v___x_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_a_900_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_891_, 1);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_array_get_borrowed(v___x_825_, v_a_900_, v___x_901_);
lean_inc(v___x_902_);
v___x_903_ = l_Lean_Name_fromJson_x3f(v___x_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_900_);
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_912_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_903_, 1);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_array_get(v___x_825_, v_a_900_, v___x_913_);
lean_dec(v_a_900_);
v___x_915_ = l_Lean_Json_getStr_x3f(v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_912_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_915_, 1);
v___x_925_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_924_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_912_);
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_a_934_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_942_ == 0)
{
v___x_936_ = v___x_925_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_925_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_912_);
lean_ctor_set(v___x_938_, 1, v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
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
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_val_821_);
v___x_943_ = lean_unsigned_to_nat(1u);
v___x_944_ = lean_box(0);
v___x_945_ = l_Lean_Json_parseCtorFields(v_json_818_, v___x_828_, v___x_943_, v___x_944_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_del_object(v___x_823_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_945_, 1);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get(v___x_825_, v_a_954_, v___x_955_);
lean_dec(v_a_954_);
v___x_957_ = l_Lean_Name_fromJson_x3f(v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_del_object(v___x_823_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_976_; 
v_a_966_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_976_ == 0)
{
v___x_968_ = v___x_957_;
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_957_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_976_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v_a_966_);
v___x_971_ = v___x_823_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_975_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_971_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec(v_val_821_);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_box(0);
v___x_979_ = l_Lean_Json_parseCtorFields(v_json_818_, v___x_826_, v___x_977_, v___x_978_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_823_);
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
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
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_a_988_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_979_, 1);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get(v___x_825_, v_a_988_, v___x_989_);
lean_dec(v_a_988_);
v___x_991_ = l_Lean_Json_getStr_x3f(v___x_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_del_object(v___x_823_);
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_991_, 1);
v___x_1001_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_823_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1020_; 
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1020_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1020_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 3);
lean_ctor_set(v___x_823_, 0, v_a_1010_);
v___x_1015_ = v___x_823_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
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
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalLocation_toJson(lean_object* v_x_1024_){
_start:
{
switch(lean_obj_tag(v_x_1024_))
{
case 0:
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1039_; 
v_a_1025_ = lean_ctor_get(v_x_1024_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1027_ = v_x_1024_;
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v_x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1039_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1029_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_1030_ = 1;
v___x_1031_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1025_, v___x_1030_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 3);
lean_ctor_set(v___x_1027_, 0, v___x_1031_);
v___x_1033_ = v___x_1027_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1029_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_Json_mkObj(v___x_1036_);
lean_dec_ref_known(v___x_1036_, 2);
return v___x_1037_;
}
}
}
case 1:
{
lean_object* v_a_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1062_; 
v_a_1040_ = lean_ctor_get(v_x_1024_, 0);
v_a_1041_ = lean_ctor_get(v_x_1024_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1043_ = v_x_1024_;
v_isShared_1044_ = v_isSharedCheck_1062_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_inc(v_a_1040_);
lean_dec(v_x_1024_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1062_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1045_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_1046_ = 1;
v___x_1047_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1040_, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = l_Lean_SubExpr_Pos_toString(v_a_1041_);
lean_dec(v_a_1041_);
v___x_1050_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(2u);
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1051_);
v___x_1053_ = lean_array_push(v___x_1052_, v___x_1048_);
v___x_1054_ = lean_array_push(v___x_1053_, v___x_1050_);
v___x_1055_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 0);
lean_ctor_set(v___x_1043_, 1, v___x_1055_);
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1057_ = v___x_1043_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Json_mkObj(v___x_1059_);
lean_dec_ref_known(v___x_1059_, 2);
return v___x_1060_;
}
}
}
case 2:
{
lean_object* v_a_1063_; lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1085_; 
v_a_1063_ = lean_ctor_get(v_x_1024_, 0);
v_a_1064_ = lean_ctor_get(v_x_1024_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1066_ = v_x_1024_;
v_isShared_1067_ = v_isSharedCheck_1085_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_inc(v_a_1063_);
lean_dec(v_x_1024_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1085_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1068_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_1069_ = 1;
v___x_1070_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1063_, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = l_Lean_SubExpr_Pos_toString(v_a_1064_);
lean_dec(v_a_1064_);
v___x_1073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
v___x_1074_ = lean_unsigned_to_nat(2u);
v___x_1075_ = lean_mk_empty_array_with_capacity(v___x_1074_);
v___x_1076_ = lean_array_push(v___x_1075_, v___x_1071_);
v___x_1077_ = lean_array_push(v___x_1076_, v___x_1073_);
v___x_1078_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
lean_ctor_set(v___x_1066_, 1, v___x_1078_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1080_ = v___x_1066_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_Json_mkObj(v___x_1082_);
lean_dec_ref_known(v___x_1082_, 2);
return v___x_1083_;
}
}
}
default: 
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v_a_1086_ = lean_ctor_get(v_x_1024_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1024_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1088_ = v_x_1024_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v_x_1024_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_1091_ = l_Lean_SubExpr_Pos_toString(v_a_1086_);
lean_dec(v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1090_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_Json_mkObj(v___x_1096_);
lean_dec_ref_known(v___x_1096_, 2);
return v___x_1097_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(lean_object* v_j_1102_, lean_object* v_k_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = l_Lean_Json_getObjValD(v_j_1102_, v_k_1103_);
v___x_1105_ = l_Lean_Name_fromJson_x3f(v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1105_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1105_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0___boxed(lean_object* v_j_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_j_1122_, v_k_1123_);
lean_dec_ref(v_k_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(lean_object* v_j_1125_, lean_object* v_k_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = l_Lean_Json_getObjValD(v_j_1125_, v_k_1126_);
v___x_1128_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1___boxed(lean_object* v_j_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_j_1129_, v_k_1130_);
lean_dec_ref(v_k_1130_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = 1;
v___x_1141_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4));
v___x_1142_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6));
v___x_1145_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5);
v___x_1146_ = lean_string_append(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = 1;
v___x_1150_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8));
v___x_1151_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9);
v___x_1153_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1154_ = lean_string_append(v___x_1153_, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1157_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10);
v___x_1158_ = lean_string_append(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = 1;
v___x_1163_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14));
v___x_1164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15);
v___x_1166_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1167_ = lean_string_append(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1169_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16);
v___x_1170_ = lean_string_append(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson(lean_object* v_json_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
lean_inc(v_json_1171_);
v___x_1173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_json_1171_, v___x_1172_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_json_1171_);
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1183_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12);
v___x_1179_ = lean_string_append(v___x_1178_, v_a_1174_);
lean_dec(v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_dec(v_json_1171_);
v_a_1184_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1173_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1173_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set_tag(v___x_1186_, 0);
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1192_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1173_, 1);
v___x_1193_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1194_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_json_1171_, v___x_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1192_);
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1204_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17);
v___x_1200_ = lean_string_append(v___x_1199_, v_a_1195_);
lean_dec(v_a_1195_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1192_);
v_a_1205_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1194_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1194_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 0);
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_a_1213_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v___x_1194_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1194_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v_a_1192_);
lean_ctor_set(v___x_1217_, 1, v_a_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
if (lean_obj_tag(v_a_1224_) == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_array_to_list(v_a_1225_);
return v___x_1226_;
}
else
{
lean_object* v_head_1227_; lean_object* v_tail_1228_; lean_object* v___x_1229_; 
v_head_1227_ = lean_ctor_get(v_a_1224_, 0);
lean_inc(v_head_1227_);
v_tail_1228_ = lean_ctor_get(v_a_1224_, 1);
lean_inc(v_tail_1228_);
lean_dec_ref_known(v_a_1224_, 2);
v___x_1229_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1225_, v_head_1227_);
v_a_1224_ = v_tail_1228_;
v_a_1225_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalsLocation_toJson(lean_object* v_x_1233_){
_start:
{
lean_object* v_mvarId_1234_; lean_object* v_loc_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1257_; 
v_mvarId_1234_ = lean_ctor_get(v_x_1233_, 0);
v_loc_1235_ = lean_ctor_get(v_x_1233_, 1);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_x_1233_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1237_ = v_x_1233_;
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_loc_1235_);
lean_inc(v_mvarId_1234_);
lean_dec(v_x_1233_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1257_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1239_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
v___x_1240_ = 1;
v___x_1241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1234_, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1242_);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1244_ = v___x_1237_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1248_ = l_Lean_SubExpr_instToJsonGoalLocation_toJson(v_loc_1235_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1247_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1245_);
v___x_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v___x_1245_);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1246_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0));
v___x_1254_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(v___x_1252_, v___x_1253_);
v___x_1255_ = l_Lean_Json_mkObj(v___x_1254_);
lean_dec(v___x_1254_);
return v___x_1255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0(lean_object* v_p_1260_, lean_object* v_visit_1261_, lean_object* v_arg_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_1260_);
v___x_1265_ = lean_apply_2(v_visit_1261_, v___x_1264_, v_arg_1262_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed(lean_object* v_p_1266_, lean_object* v_visit_1267_, lean_object* v_arg_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Expr_traverseAppWithPos___redArg___lam__0(v_p_1266_, v_visit_1267_, v_arg_1268_, v_x_1269_);
lean_dec(v_p_1266_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object* v_inst_1271_, lean_object* v_visit_1272_, lean_object* v_p_1273_, lean_object* v_e_1274_){
_start:
{
if (lean_obj_tag(v_e_1274_) == 5)
{
lean_object* v_toApplicative_1275_; lean_object* v_toFunctor_1276_; lean_object* v_toSeq_1277_; lean_object* v_fn_1278_; lean_object* v_arg_1279_; lean_object* v_map_1280_; lean_object* v___f_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_toApplicative_1275_ = lean_ctor_get(v_inst_1271_, 0);
v_toFunctor_1276_ = lean_ctor_get(v_toApplicative_1275_, 0);
v_toSeq_1277_ = lean_ctor_get(v_toApplicative_1275_, 2);
lean_inc(v_toSeq_1277_);
v_fn_1278_ = lean_ctor_get(v_e_1274_, 0);
lean_inc_ref(v_fn_1278_);
v_arg_1279_ = lean_ctor_get(v_e_1274_, 1);
v_map_1280_ = lean_ctor_get(v_toFunctor_1276_, 0);
lean_inc(v_map_1280_);
lean_inc_ref(v_arg_1279_);
lean_inc(v_visit_1272_);
lean_inc(v_p_1273_);
v___f_1281_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1281_, 0, v_p_1273_);
lean_closure_set(v___f_1281_, 1, v_visit_1272_);
lean_closure_set(v___f_1281_, 2, v_arg_1279_);
v___x_1282_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_1282_, 0, v_e_1274_);
v___x_1283_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_1273_);
lean_dec(v_p_1273_);
v___x_1284_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1271_, v_visit_1272_, v___x_1283_, v_fn_1278_);
v___x_1285_ = lean_apply_4(v_map_1280_, lean_box(0), lean_box(0), v___x_1282_, v___x_1284_);
v___x_1286_ = lean_apply_4(v_toSeq_1277_, lean_box(0), lean_box(0), v___x_1285_, v___f_1281_);
return v___x_1286_;
}
else
{
lean_object* v___x_1287_; 
lean_dec_ref(v_inst_1271_);
v___x_1287_ = lean_apply_2(v_visit_1272_, v_p_1273_, v_e_1274_);
return v___x_1287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object* v_M_1288_, lean_object* v_inst_1289_, lean_object* v_visit_1290_, lean_object* v_p_1291_, lean_object* v_e_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1289_, v_visit_1290_, v_p_1291_, v_e_1292_);
return v___x_1293_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
