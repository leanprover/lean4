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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___impl___boxed(lean_object*);
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
uint8_t l_Lean_SubExpr_Pos_isRoot(lean_object* v_p_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_unsigned_to_nat(4u);
v___x_10_ = lean_nat_dec_lt(v_p_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT void l_Lean_SubExpr_Pos_isRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_8_ = stack[0].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_SubExpr_Pos_isRoot(v_p_8_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_isRoot___boxed(lean_object* v_p_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_SubExpr_Pos_isRoot(v_p_12_);
lean_dec(v_p_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_head_spec__0(lean_object* v_msg_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_panic_fn_borrowed(v___x_16_, v_msg_15_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_head___closed__3(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_21_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__2));
v___x_22_ = lean_unsigned_to_nat(19u);
v___x_23_ = lean_unsigned_to_nat(46u);
v___x_24_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__1));
v___x_25_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_26_ = l_mkPanicMessageWithDecl(v___x_25_, v___x_24_, v___x_23_, v___x_22_, v___x_21_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head(lean_object* v_p_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_Lean_SubExpr_Pos_isRoot(v_p_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(4u);
v___x_30_ = lean_nat_mod(v_p_27_, v___x_29_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_Lean_SubExpr_Pos_head___closed__3, &l_Lean_SubExpr_Pos_head___closed__3_once, _init_l_Lean_SubExpr_Pos_head___closed__3);
v___x_32_ = l_panic___at___00Lean_SubExpr_Pos_head_spec__0(v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_head___boxed(lean_object* v_p_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_SubExpr_Pos_head(v_p_33_);
lean_dec(v_p_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(lean_object* v_msg_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_panic_fn_borrowed(v___x_36_, v_msg_35_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_tail___closed__1(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_39_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__2));
v___x_40_ = lean_unsigned_to_nat(19u);
v___x_41_ = lean_unsigned_to_nat(50u);
v___x_42_ = ((lean_object*)(l_Lean_SubExpr_Pos_tail___closed__0));
v___x_43_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_44_ = l_mkPanicMessageWithDecl(v___x_43_, v___x_42_, v___x_41_, v___x_40_, v___x_39_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail(lean_object* v_p_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_SubExpr_Pos_isRoot(v_p_45_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = l_Lean_SubExpr_Pos_head(v_p_45_);
v___x_48_ = lean_nat_sub(v_p_45_, v___x_47_);
lean_dec(v___x_47_);
v___x_49_ = lean_unsigned_to_nat(2u);
v___x_50_ = lean_nat_shiftr(v___x_48_, v___x_49_);
lean_dec(v___x_48_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_obj_once(&l_Lean_SubExpr_Pos_tail___closed__1, &l_Lean_SubExpr_Pos_tail___closed__1_once, _init_l_Lean_SubExpr_Pos_tail___closed__1);
v___x_52_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_tail___boxed(lean_object* v_p_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_SubExpr_Pos_tail(v_p_53_);
lean_dec(v_p_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push(lean_object* v_p_57_, lean_object* v_c_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(4u);
v___x_60_ = lean_nat_dec_le(v___x_59_, v_c_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_nat_mul(v_p_57_, v___x_59_);
v___x_62_ = lean_nat_add(v___x_61_, v_c_58_);
lean_dec(v_c_58_);
lean_dec(v___x_61_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_63_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_64_ = ((lean_object*)(l_Lean_SubExpr_Pos_push___closed__0));
v___x_65_ = lean_unsigned_to_nat(54u);
v___x_66_ = lean_unsigned_to_nat(27u);
v___x_67_ = ((lean_object*)(l_Lean_SubExpr_Pos_push___closed__1));
v___x_68_ = l_Nat_reprFast(v_c_58_);
v___x_69_ = lean_string_append(v___x_67_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_70_ = l_mkPanicMessageWithDecl(v___x_63_, v___x_64_, v___x_65_, v___x_66_, v___x_69_);
lean_dec_ref(v___x_69_);
v___x_71_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_push___boxed(lean_object* v_p_72_, lean_object* v_c_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_SubExpr_Pos_push(v_p_72_, v_c_73_);
lean_dec(v_p_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg(lean_object* v_f_75_, lean_object* v_init_76_, lean_object* v_p_77_){
_start:
{
uint8_t v___x_78_; 
v___x_78_ = l_Lean_SubExpr_Pos_isRoot(v_p_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_79_ = l_Lean_SubExpr_Pos_tail(v_p_77_);
lean_inc(v_f_75_);
v___x_80_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_75_, v_init_76_, v___x_79_);
lean_dec(v___x_79_);
v___x_81_ = l_Lean_SubExpr_Pos_head(v_p_77_);
v___x_82_ = lean_apply_2(v_f_75_, v___x_80_, v___x_81_);
return v___x_82_;
}
else
{
lean_dec(v_f_75_);
lean_inc(v_init_76_);
return v_init_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___redArg___boxed(lean_object* v_f_83_, lean_object* v_init_84_, lean_object* v_p_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_83_, v_init_84_, v_p_85_);
lean_dec(v_p_85_);
lean_dec(v_init_84_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl(lean_object* v_00_u03b1_87_, lean_object* v_f_88_, lean_object* v_init_89_, lean_object* v_p_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_88_, v_init_89_, v_p_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldl___boxed(lean_object* v_00_u03b1_92_, lean_object* v_f_93_, lean_object* v_init_94_, lean_object* v_p_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_SubExpr_Pos_foldl(v_00_u03b1_92_, v_f_93_, v_init_94_, v_p_95_);
lean_dec(v_p_95_);
lean_dec(v_init_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr___redArg(lean_object* v_f_97_, lean_object* v_p_98_, lean_object* v_init_99_){
_start:
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_SubExpr_Pos_isRoot(v_p_98_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = l_Lean_SubExpr_Pos_tail(v_p_98_);
v___x_102_ = l_Lean_SubExpr_Pos_head(v_p_98_);
lean_dec(v_p_98_);
lean_inc(v_f_97_);
v___x_103_ = lean_apply_2(v_f_97_, v___x_102_, v_init_99_);
v_p_98_ = v___x_101_;
v_init_99_ = v___x_103_;
goto _start;
}
else
{
lean_dec(v_p_98_);
lean_dec(v_f_97_);
return v_init_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldr(lean_object* v_00_u03b1_105_, lean_object* v_f_106_, lean_object* v_p_107_, lean_object* v_init_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_SubExpr_Pos_foldr___redArg(v_f_106_, v_p_107_, v_init_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(lean_object* v_p_110_, lean_object* v_f_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = l_Lean_SubExpr_Pos_head(v_p_110_);
v___x_114_ = lean_apply_2(v_f_111_, v_x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed(lean_object* v_p_115_, lean_object* v_f_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(v_p_115_, v_f_116_, v_x_117_);
lean_dec(v_p_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___redArg(lean_object* v_inst_119_, lean_object* v_f_120_, lean_object* v_init_121_, lean_object* v_p_122_){
_start:
{
lean_object* v_toApplicative_123_; lean_object* v_toBind_124_; lean_object* v_toPure_125_; uint8_t v___x_126_; 
v_toApplicative_123_ = lean_ctor_get(v_inst_119_, 0);
v_toBind_124_ = lean_ctor_get(v_inst_119_, 1);
lean_inc(v_toBind_124_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_123_, 1);
v___x_126_ = l_Lean_SubExpr_Pos_isRoot(v_p_122_);
if (v___x_126_ == 0)
{
lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_inc(v_f_120_);
lean_inc(v_p_122_);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_127_, 0, v_p_122_);
lean_closure_set(v___f_127_, 1, v_f_120_);
v___x_128_ = l_Lean_SubExpr_Pos_tail(v_p_122_);
lean_dec(v_p_122_);
v___x_129_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_119_, v_f_120_, v_init_121_, v___x_128_);
v___x_130_ = lean_apply_4(v_toBind_124_, lean_box(0), lean_box(0), v___x_129_, v___f_127_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
lean_inc(v_toPure_125_);
lean_dec(v_toBind_124_);
lean_dec(v_p_122_);
lean_dec(v_f_120_);
lean_dec_ref(v_inst_119_);
v___x_131_ = lean_apply_2(v_toPure_125_, lean_box(0), v_init_121_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_M_134_, lean_object* v_inst_135_, lean_object* v_f_136_, lean_object* v_init_137_, lean_object* v_p_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_135_, v_f_136_, v_init_137_, v_p_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldlM___boxed(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_M_142_, lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_init_145_, lean_object* v_p_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_SubExpr_Pos_foldlM(v_00_u03b1_140_, v_inst_141_, v_M_142_, v_inst_143_, v_f_144_, v_init_145_, v_p_146_);
lean_dec(v_inst_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg___boxed(lean_object* v_inst_148_, lean_object* v_f_149_, lean_object* v_p_150_, lean_object* v_init_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_148_, v_f_149_, v_p_150_, v_init_151_);
lean_dec(v_p_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___redArg(lean_object* v_inst_153_, lean_object* v_f_154_, lean_object* v_p_155_, lean_object* v_init_156_){
_start:
{
lean_object* v_toApplicative_157_; lean_object* v_toBind_158_; lean_object* v_toPure_159_; uint8_t v___x_160_; 
v_toApplicative_157_ = lean_ctor_get(v_inst_153_, 0);
v_toBind_158_ = lean_ctor_get(v_inst_153_, 1);
lean_inc(v_toBind_158_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_157_, 1);
v___x_160_ = l_Lean_SubExpr_Pos_isRoot(v_p_155_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_161_ = l_Lean_SubExpr_Pos_head(v_p_155_);
lean_inc(v_f_154_);
v___x_162_ = lean_apply_2(v_f_154_, v___x_161_, v_init_156_);
v___x_163_ = l_Lean_SubExpr_Pos_tail(v_p_155_);
v___x_164_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_foldrM___redArg___boxed), 4, 3);
lean_closure_set(v___x_164_, 0, v_inst_153_);
lean_closure_set(v___x_164_, 1, v_f_154_);
lean_closure_set(v___x_164_, 2, v___x_163_);
v___x_165_ = lean_apply_4(v_toBind_158_, lean_box(0), lean_box(0), v___x_162_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
lean_inc(v_toPure_159_);
lean_dec(v_toBind_158_);
lean_dec(v_f_154_);
lean_dec_ref(v_inst_153_);
v___x_166_ = lean_apply_2(v_toPure_159_, lean_box(0), v_init_156_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM(lean_object* v_00_u03b1_167_, lean_object* v_M_168_, lean_object* v_inst_169_, lean_object* v_f_170_, lean_object* v_p_171_, lean_object* v_init_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_169_, v_f_170_, v_p_171_, v_init_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___boxed(lean_object* v_00_u03b1_174_, lean_object* v_M_175_, lean_object* v_inst_176_, lean_object* v_f_177_, lean_object* v_p_178_, lean_object* v_init_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_SubExpr_Pos_foldrM(v_00_u03b1_174_, v_M_175_, v_inst_176_, v_f_177_, v_p_178_, v_init_179_);
lean_dec(v_p_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0(lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_add(v___y_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth___lam__0___boxed(lean_object* v_x_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_SubExpr_Pos_depth___lam__0(v_x_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec(v_x_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_depth(lean_object* v_p_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___f_190_ = ((lean_object*)(l_Lean_SubExpr_Pos_depth___closed__0));
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_Lean_SubExpr_Pos_foldr___redArg(v___f_190_, v_p_189_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___lam__0(lean_object* v_pred_193_, lean_object* v_n_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_apply_1(v_pred_193_, v_n_194_);
v___x_197_ = lean_unbox(v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_a_195_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(lean_object* v_f_200_, lean_object* v_p_201_, lean_object* v_init_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = l_Lean_SubExpr_Pos_isRoot(v_p_201_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = l_Lean_SubExpr_Pos_head(v_p_201_);
lean_inc_ref(v_f_200_);
v___x_205_ = lean_apply_2(v_f_200_, v___x_204_, v_init_202_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_dec(v_p_201_);
lean_dec_ref(v_f_200_);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; 
v_val_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_206_);
lean_dec_ref_known(v___x_205_, 1);
v___x_207_ = l_Lean_SubExpr_Pos_tail(v_p_201_);
lean_dec(v_p_201_);
v_p_201_ = v___x_207_;
v_init_202_ = v_val_206_;
goto _start;
}
}
else
{
lean_object* v___x_209_; 
lean_dec(v_p_201_);
lean_dec_ref(v_f_200_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v_init_202_);
return v___x_209_;
}
}
}
uint8_t l_Lean_SubExpr_Pos_all(lean_object* v_pred_210_, lean_object* v_p_211_){
_start:
{
lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___f_212_ = lean_alloc_closure((void*)(l_Lean_SubExpr_Pos_all___lam__0), 3, 1);
lean_closure_set(v___f_212_, 0, v_pred_210_);
v___x_213_ = lean_box(0);
v___x_214_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(v___f_212_, v_p_211_, v___x_213_);
if (lean_obj_tag(v___x_214_) == 0)
{
uint8_t v___x_215_; 
v___x_215_ = 0;
return v___x_215_;
}
else
{
uint8_t v___x_216_; 
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = 1;
return v___x_216_;
}
}
}
LEAN_EXPORT void l_Lean_SubExpr_Pos_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_pred_210_ = stack[0].m_obj;
lean_object* v_p_211_ = stack[1].m_obj;
uint8_t v_res_217_;
v_res_217_ = l_Lean_SubExpr_Pos_all(v_pred_210_, v_p_211_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_all___boxed(lean_object* v_pred_218_, lean_object* v_p_219_){
_start:
{
uint8_t v_res_220_; lean_object* v_r_221_; 
v_res_220_ = l_Lean_SubExpr_Pos_all(v_pred_218_, v_p_219_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0(lean_object* v_00_u03b1_222_, lean_object* v_f_223_, lean_object* v_p_224_, lean_object* v_init_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(v_f_223_, v_p_224_, v_init_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append(lean_object* v_init_228_, lean_object* v_p_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l_Lean_SubExpr_Pos_append___closed__0));
v___x_231_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_230_, v_init_228_, v_p_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_append___boxed(lean_object* v_init_232_, lean_object* v_p_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_SubExpr_Pos_append(v_init_232_, v_p_233_);
lean_dec(v_p_233_);
lean_dec(v_init_232_);
return v_res_234_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(lean_object* v_as_235_, size_t v_i_236_, size_t v_stop_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_eq(v_i_236_, v_stop_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; 
v___x_240_ = lean_array_uget_borrowed(v_as_235_, v_i_236_);
lean_inc(v___x_240_);
v___x_241_ = l_Lean_SubExpr_Pos_push(v_b_238_, v___x_240_);
lean_dec(v_b_238_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_add(v_i_236_, v___x_242_);
v_i_236_ = v___x_243_;
v_b_238_ = v___x_241_;
goto _start;
}
else
{
return v_b_238_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_235_ = stack[0].m_obj;
size_t v_i_236_ = stack[1].m_num;
size_t v_stop_237_ = stack[2].m_num;
lean_object* v_b_238_ = stack[3].m_obj;
lean_object* v_res_245_;
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_as_235_, v_i_236_, v_stop_237_, v_b_238_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0___boxed(lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_stop_248_, lean_object* v_b_249_){
_start:
{
size_t v_i_boxed_250_; size_t v_stop_boxed_251_; lean_object* v_res_252_; 
v_i_boxed_250_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_stop_boxed_251_ = lean_unbox_usize(v_stop_248_);
lean_dec(v_stop_248_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_as_246_, v_i_boxed_250_, v_stop_boxed_251_, v_b_249_);
lean_dec_ref(v_as_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray(lean_object* v_ps_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_array_get_size(v_ps_253_);
v___x_257_ = lean_nat_dec_lt(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
return v___x_254_;
}
else
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_le(v___x_256_, v___x_256_);
if (v___x_258_ == 0)
{
if (v___x_257_ == 0)
{
return v___x_254_;
}
else
{
size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; 
v___x_259_ = ((size_t)0ULL);
v___x_260_ = lean_usize_of_nat(v___x_256_);
v___x_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_253_, v___x_259_, v___x_260_, v___x_254_);
return v___x_261_;
}
}
else
{
size_t v___x_262_; size_t v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((size_t)0ULL);
v___x_263_ = lean_usize_of_nat(v___x_256_);
v___x_264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_253_, v___x_262_, v___x_263_, v___x_254_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_ofArray___boxed(lean_object* v_ps_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_SubExpr_Pos_ofArray(v_ps_265_);
lean_dec_ref(v_ps_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray(lean_object* v_p_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l_Lean_SubExpr_Pos_toArray___closed__0));
v___x_272_ = ((lean_object*)(l_Lean_SubExpr_Pos_toArray___closed__1));
v___x_273_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_271_, v___x_272_, v_p_270_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toArray___boxed(lean_object* v_p_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_SubExpr_Pos_toArray(v_p_274_);
lean_dec(v_p_274_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object* v_p_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = l_Lean_SubExpr_Pos_push(v_p_276_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingDomain___boxed(lean_object* v_p_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_279_);
lean_dec(v_p_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object* v_p_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = l_Lean_SubExpr_Pos_push(v_p_281_, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushBindingBody___boxed(lean_object* v_p_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_284_);
lean_dec(v_p_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object* v_p_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Lean_SubExpr_Pos_push(v_p_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetVarType___boxed(lean_object* v_p_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_289_);
lean_dec(v_p_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object* v_p_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = l_Lean_SubExpr_Pos_push(v_p_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetValue___boxed(lean_object* v_p_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_294_);
lean_dec(v_p_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object* v_p_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = l_Lean_SubExpr_Pos_push(v_p_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushLetBody___boxed(lean_object* v_p_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_299_);
lean_dec(v_p_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn(lean_object* v_p_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = l_Lean_SubExpr_Pos_push(v_p_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppFn___boxed(lean_object* v_p_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_304_);
lean_dec(v_p_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg(lean_object* v_p_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = l_Lean_SubExpr_Pos_push(v_p_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushAppArg___boxed(lean_object* v_p_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_309_);
lean_dec(v_p_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object* v_p_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Lean_SubExpr_Pos_push(v_p_311_, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushProj___boxed(lean_object* v_p_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_SubExpr_Pos_pushProj(v_p_314_);
lean_dec(v_p_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType(lean_object* v_p_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = l_Lean_SubExpr_Pos_push(v_p_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushType___boxed(lean_object* v_p_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_SubExpr_Pos_pushType(v_p_319_);
lean_dec(v_p_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object* v_numArgs_321_, lean_object* v_p_322_){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_nat_pow(v___x_323_, v_numArgs_321_);
v___x_325_ = lean_nat_mul(v_p_322_, v___x_324_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryFn___boxed(lean_object* v_numArgs_326_, lean_object* v_p_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_SubExpr_Pos_pushNaryFn(v_numArgs_326_, v_p_327_);
lean_dec(v_p_327_);
lean_dec(v_numArgs_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object* v_numArgs_329_, lean_object* v_argIdx_330_, lean_object* v_p_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_this_337_; 
v___x_332_ = lean_unsigned_to_nat(4u);
v___x_333_ = lean_nat_sub(v_numArgs_329_, v_argIdx_330_);
v___x_334_ = lean_nat_pow(v___x_332_, v___x_333_);
lean_dec(v___x_333_);
v___x_335_ = lean_nat_mul(v_p_331_, v___x_334_);
lean_dec(v___x_334_);
v___x_336_ = lean_unsigned_to_nat(1u);
v_this_337_ = lean_nat_add(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
return v_this_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNaryArg___boxed(lean_object* v_numArgs_338_, lean_object* v_argIdx_339_, lean_object* v_p_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_SubExpr_Pos_pushNaryArg(v_numArgs_338_, v_argIdx_339_, v_p_340_);
lean_dec(v_p_340_);
lean_dec(v_argIdx_339_);
lean_dec(v_numArgs_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingDomain(lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
lean_object* v_zero_344_; uint8_t v_isZero_345_; 
v_zero_344_ = lean_unsigned_to_nat(0u);
v_isZero_345_ = lean_nat_dec_eq(v_x_342_, v_zero_344_);
if (v_isZero_345_ == 1)
{
lean_object* v___x_346_; 
lean_dec(v_x_342_);
v___x_346_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_x_343_);
lean_dec(v_x_343_);
return v___x_346_;
}
else
{
lean_object* v_one_347_; lean_object* v_n_348_; lean_object* v___x_349_; 
v_one_347_ = lean_unsigned_to_nat(1u);
v_n_348_ = lean_nat_sub(v_x_342_, v_one_347_);
lean_dec(v_x_342_);
v___x_349_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_343_);
lean_dec(v_x_343_);
v_x_342_ = v_n_348_;
v_x_343_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_pushNthBindingBody(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_zero_353_; uint8_t v_isZero_354_; 
v_zero_353_ = lean_unsigned_to_nat(0u);
v_isZero_354_ = lean_nat_dec_eq(v_x_351_, v_zero_353_);
if (v_isZero_354_ == 1)
{
lean_dec(v_x_351_);
return v_x_352_;
}
else
{
lean_object* v_one_355_; lean_object* v_n_356_; lean_object* v___x_357_; 
v_one_355_ = lean_unsigned_to_nat(1u);
v_n_356_ = lean_nat_sub(v_x_351_, v_one_355_);
lean_dec(v_x_351_);
v___x_357_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_352_);
lean_dec(v_x_352_);
v_x_351_ = v_n_356_;
v_x_352_ = v___x_357_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
if (lean_obj_tag(v_a_359_) == 0)
{
lean_object* v___x_361_; 
v___x_361_ = l_List_reverse___redArg(v_a_360_);
return v___x_361_;
}
else
{
lean_object* v_head_362_; lean_object* v_tail_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_372_; 
v_head_362_ = lean_ctor_get(v_a_359_, 0);
v_tail_363_ = lean_ctor_get(v_a_359_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_a_359_);
if (v_isSharedCheck_372_ == 0)
{
v___x_365_ = v_a_359_;
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_tail_363_);
lean_inc(v_head_362_);
lean_dec(v_a_359_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = l_Nat_reprFast(v_head_362_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v_a_360_);
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_360_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v_a_359_ = v_tail_363_;
v_a_360_ = v___x_369_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString(lean_object* v_p_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_375_ = ((lean_object*)(l_Lean_SubExpr_Pos_toString___closed__0));
v___x_376_ = l_Lean_SubExpr_Pos_toArray(v_p_374_);
v___x_377_ = lean_array_to_list(v___x_376_);
v___x_378_ = lean_box(0);
v___x_379_ = l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(v___x_377_, v___x_378_);
v___x_380_ = l_String_intercalate(v___x_375_, v___x_379_);
v___x_381_ = lean_string_append(v___x_375_, v___x_380_);
lean_dec_ref(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_toString___boxed(lean_object* v_p_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_SubExpr_Pos_toString(v_p_382_);
lean_dec(v_p_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(lean_object* v_x_397_){
_start:
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0));
v___x_399_ = lean_string_dec_eq(v_x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1));
v___x_401_ = lean_string_dec_eq(v_x_397_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2));
v___x_403_ = lean_string_dec_eq(v_x_397_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3));
v___x_405_ = lean_string_dec_eq(v_x_397_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4));
v___x_407_ = lean_string_append(v___x_406_, v_x_397_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
v___x_409_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5));
return v___x_409_;
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6));
return v___x_410_;
}
}
else
{
lean_object* v___x_411_; 
v___x_411_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7));
return v___x_411_;
}
}
else
{
lean_object* v___x_412_; 
v___x_412_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8));
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_x_413_);
lean_dec_ref(v_x_413_);
return v_res_414_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg(){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___closed__0));
return v___x_418_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_419_;
v_res_419_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg___boxed(lean_object* v___dummy_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
return v_res_421_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___redArg();
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(lean_object* v_s_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___boxed(lean_object* v_s_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v_s_425_);
lean_dec_ref(v_s_425_);
return v_res_426_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(size_t v_sz_427_, size_t v_i_428_, lean_object* v_bs_429_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_428_, v_sz_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_bs_429_);
return v___x_431_;
}
else
{
lean_object* v_v_432_; lean_object* v___x_433_; 
v_v_432_ = lean_array_uget_borrowed(v_bs_429_, v_i_428_);
v___x_433_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_v_432_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_bs_429_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
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
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v_bs_x27_444_; size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v_a_442_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_433_, 1);
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_429_, v_i_428_, v___x_443_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = lean_usize_add(v_i_428_, v___x_445_);
v___x_447_ = lean_array_uset(v_bs_x27_444_, v_i_428_, v_a_442_);
v_i_428_ = v___x_446_;
v_bs_429_ = v___x_447_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_427_ = stack[0].m_num;
size_t v_i_428_ = stack[1].m_num;
lean_object* v_bs_429_ = stack[2].m_obj;
lean_object* v_res_449_;
v_res_449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_427_, v_i_428_, v_bs_429_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3___boxed(lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_bs_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_454_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_boxed_453_, v_i_boxed_454_, v_bs_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
return v_x_457_;
}
else
{
lean_object* v_head_459_; lean_object* v_tail_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_head_459_ = lean_ctor_get(v_x_458_, 0);
v_tail_460_ = lean_ctor_get(v_x_458_, 1);
v___x_461_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0));
v___x_462_ = lean_string_append(v_x_457_, v___x_461_);
v___x_463_ = lean_string_append(v___x_462_, v_head_459_);
v_x_457_ = v___x_463_;
v_x_458_ = v_tail_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___boxed(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v_x_465_, v_x_466_);
lean_dec(v_x_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0));
return v___x_472_;
}
else
{
lean_object* v_tail_473_; 
v_tail_473_ = lean_ctor_get(v_x_471_, 1);
if (lean_obj_tag(v_tail_473_) == 0)
{
lean_object* v_head_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_head_474_ = lean_ctor_get(v_x_471_, 0);
v___x_475_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_476_ = lean_string_append(v___x_475_, v_head_474_);
v___x_477_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
return v___x_478_;
}
else
{
lean_object* v_head_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint32_t v___x_483_; lean_object* v___x_484_; 
v_head_479_ = lean_ctor_get(v_x_471_, 0);
v___x_480_ = ((lean_object*)(l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1));
v___x_481_ = lean_string_append(v___x_480_, v_head_479_);
v___x_482_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v___x_481_, v_tail_473_);
v___x_483_ = 93;
v___x_484_ = lean_string_push(v___x_482_, v___x_483_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___boxed(lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_x_485_);
lean_dec(v_x_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(lean_object* v_x_487_, lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v_it_493_; lean_object* v_startInclusive_494_; lean_object* v_endExclusive_495_; 
if (lean_obj_tag(v_a_490_) == 0)
{
lean_object* v_currPos_500_; lean_object* v_searcher_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_524_; 
v_currPos_500_ = lean_ctor_get(v_a_490_, 0);
v_searcher_501_ = lean_ctor_get(v_a_490_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_524_ == 0)
{
v___x_503_ = v_a_490_;
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_searcher_501_);
lean_inc(v_currPos_500_);
lean_dec(v_a_490_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_524_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v_decide_505_; 
v_decide_505_ = lean_nat_dec_eq(v_searcher_501_, v___x_489_);
if (v_decide_505_ == 0)
{
uint32_t v___x_506_; uint32_t v___x_507_; uint8_t v___x_508_; 
v___x_506_ = 47;
v___x_507_ = lean_string_utf8_get_fast(v_x_487_, v_searcher_501_);
v___x_508_ = lean_uint32_dec_eq(v___x_507_, v___x_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_string_utf8_next_fast(v_x_487_, v_searcher_501_);
lean_dec(v_searcher_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_509_);
v___x_511_ = v___x_503_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_currPos_500_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
v_a_490_ = v___x_511_;
goto _start;
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v_slice_517_; lean_object* v_nextIt_519_; 
v___x_514_ = lean_string_utf8_next_fast(v_x_487_, v_searcher_501_);
v___x_515_ = lean_nat_sub(v___x_514_, v_searcher_501_);
v___x_516_ = lean_nat_add(v_searcher_501_, v___x_515_);
lean_dec(v___x_515_);
v_slice_517_ = l_String_Slice_subslice_x21(v___x_488_, v_currPos_500_, v_searcher_501_);
lean_inc(v___x_516_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_516_);
lean_ctor_set(v___x_503_, 0, v___x_516_);
v_nextIt_519_ = v___x_503_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_516_);
v_nextIt_519_ = v_reuseFailAlloc_522_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v_startInclusive_520_; lean_object* v_endExclusive_521_; 
v_startInclusive_520_ = lean_ctor_get(v_slice_517_, 0);
lean_inc(v_startInclusive_520_);
v_endExclusive_521_ = lean_ctor_get(v_slice_517_, 1);
lean_inc(v_endExclusive_521_);
lean_dec_ref(v_slice_517_);
v_it_493_ = v_nextIt_519_;
v_startInclusive_494_ = v_startInclusive_520_;
v_endExclusive_495_ = v_endExclusive_521_;
goto v___jp_492_;
}
}
}
else
{
lean_object* v___x_523_; 
lean_del_object(v___x_503_);
lean_dec(v_searcher_501_);
v___x_523_ = lean_box(1);
lean_inc(v___x_489_);
v_it_493_ = v___x_523_;
v_startInclusive_494_ = v_currPos_500_;
v_endExclusive_495_ = v___x_489_;
goto v___jp_492_;
}
}
}
else
{
lean_dec(v___x_489_);
lean_dec_ref(v_x_487_);
return v_b_491_;
}
v___jp_492_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_inc_ref(v_x_487_);
v___x_496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_496_, 0, v_x_487_);
lean_ctor_set(v___x_496_, 1, v_startInclusive_494_);
lean_ctor_set(v___x_496_, 2, v_endExclusive_495_);
v___x_497_ = l_String_Slice_toString(v___x_496_);
lean_dec_ref_known(v___x_496_, 3);
v___x_498_ = lean_array_push(v_b_491_, v___x_497_);
v_a_490_ = v_it_493_;
v_b_491_ = v___x_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg___boxed(lean_object* v_x_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_525_, v___x_526_, v___x_527_, v_a_528_, v_b_529_);
lean_dec_ref(v___x_526_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x3f(lean_object* v_x_535_){
_start:
{
lean_object* v_ss_537_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_SubExpr_Pos_toString___closed__0));
v___x_543_ = lean_string_dec_eq(v_x_535_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_string_utf8_byte_size(v_x_535_);
lean_inc_ref(v_x_535_);
v___x_546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_546_, 0, v_x_535_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
lean_ctor_set(v___x_546_, 2, v___x_545_);
v___x_547_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0);
v___x_548_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__1));
v___x_549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_535_, v___x_546_, v___x_545_, v___x_547_, v___x_548_);
lean_dec_ref_known(v___x_546_, 3);
v___x_550_ = lean_array_to_list(v___x_549_);
if (lean_obj_tag(v___x_550_) == 1)
{
lean_object* v_head_551_; lean_object* v_tail_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_head_551_ = lean_ctor_get(v___x_550_, 0);
v_tail_552_ = lean_ctor_get(v___x_550_, 1);
v___x_553_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__2));
v___x_554_ = lean_string_dec_eq(v_head_551_, v___x_553_);
if (v___x_554_ == 0)
{
v_ss_537_ = v___x_550_;
goto v___jp_536_;
}
else
{
lean_object* v___x_555_; size_t v_sz_556_; size_t v___x_557_; lean_object* v___x_558_; 
lean_inc(v_tail_552_);
lean_dec_ref_known(v___x_550_, 2);
v___x_555_ = lean_array_mk(v_tail_552_);
v_sz_556_ = lean_array_size(v___x_555_);
v___x_557_ = ((size_t)0ULL);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_556_, v___x_557_, v___x_555_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
else
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_a_567_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_569_ = v___x_558_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_558_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = l_Lean_SubExpr_Pos_ofArray(v_a_567_);
lean_dec(v_a_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
else
{
v_ss_537_ = v___x_550_;
goto v___jp_536_;
}
}
else
{
lean_object* v___x_576_; 
lean_dec_ref(v_x_535_);
v___x_576_ = ((lean_object*)(l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7));
return v___x_576_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_538_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x3f___closed__0));
v___x_539_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_ss_537_);
lean_dec(v_ss_537_);
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(lean_object* v_x_577_, lean_object* v___x_578_, lean_object* v___x_579_, lean_object* v_inst_580_, lean_object* v_R_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_577_, v___x_578_, v___x_579_, v_a_582_, v_b_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___boxed(lean_object* v_x_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v_inst_588_, lean_object* v_R_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(v_x_585_, v___x_586_, v___x_587_, v_inst_588_, v_R_589_, v_a_590_, v_b_591_);
lean_dec_ref(v___x_586_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_fromString_x21(lean_object* v_s_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_SubExpr_Pos_fromString_x3f(v_s_594_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_598_ = ((lean_object*)(l_Lean_SubExpr_Pos_fromString_x21___closed__0));
v___x_599_ = lean_unsigned_to_nat(140u);
v___x_600_ = lean_unsigned_to_nat(16u);
v___x_601_ = l_mkPanicMessageWithDecl(v___x_597_, v___x_598_, v___x_599_, v___x_600_, v_a_596_);
lean_dec(v_a_596_);
v___x_602_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_601_);
return v___x_602_;
}
else
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_595_, 1);
return v_a_603_;
}
}
}
uint8_t l_Lean_SubExpr_Pos_instDecidableEq(lean_object* v_a_606_, lean_object* v_b_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_nat_dec_eq(v_a_606_, v_b_607_);
return v___x_608_;
}
}
LEAN_EXPORT void l_Lean_SubExpr_Pos_instDecidableEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_606_ = stack[0].m_obj;
lean_object* v_b_607_ = stack[1].m_obj;
uint8_t v_res_609_;
v_res_609_ = l_Lean_SubExpr_Pos_instDecidableEq(v_a_606_, v_b_607_);
stack->m_num = v_res_609_;
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instDecidableEq___boxed(lean_object* v_a_610_, lean_object* v_b_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Lean_SubExpr_Pos_instDecidableEq(v_a_610_, v_b_611_);
lean_dec(v_b_611_);
lean_dec(v_a_610_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
static lean_object* _init_l_Lean_SubExpr_Pos_instEmptyCollection(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = lean_unsigned_to_nat(1u);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0(lean_object* v_p_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = ((lean_object*)(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1));
v___x_623_ = l_Lean_SubExpr_Pos_toString(v_p_620_);
v___x_624_ = l_String_quote(v___x_623_);
v___x_625_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_622_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instRepr___lam__0___boxed(lean_object* v_p_627_, lean_object* v_x_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_SubExpr_Pos_instRepr___lam__0(v_p_627_, v_x_628_);
lean_dec(v_x_628_);
lean_dec(v_p_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instToJson___lam__0(lean_object* v_s_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_633_, 0, v_s_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_Pos_instFromJson___lam__0(lean_object* v_j_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Json_getStr_x3f(v_j_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_650_; 
v_a_649_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_640_, 1);
v___x_650_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_649_);
return v___x_650_;
}
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__2(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l_Lean_instInhabitedSubExpr_default___closed__1));
v___x_658_ = l_Lean_Expr_const___override(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default___closed__3(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__2, &l_Lean_instInhabitedSubExpr_default___closed__2_once, _init_l_Lean_instInhabitedSubExpr_default___closed__2);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr_default(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_obj_once(&l_Lean_instInhabitedSubExpr_default___closed__3, &l_Lean_instInhabitedSubExpr_default___closed__3_once, _init_l_Lean_instInhabitedSubExpr_default___closed__3);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr(void){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_instInhabitedSubExpr_default;
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* v_e_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_e_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
uint8_t l_Lean_SubExpr_isRoot(lean_object* v_s_667_){
_start:
{
lean_object* v_pos_668_; uint8_t v___x_669_; 
v_pos_668_ = lean_ctor_get(v_s_667_, 1);
v___x_669_ = l_Lean_SubExpr_Pos_isRoot(v_pos_668_);
return v___x_669_;
}
}
LEAN_EXPORT void l_Lean_SubExpr_isRoot_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_667_ = stack[0].m_obj;
uint8_t v_res_670_;
v_res_670_ = l_Lean_SubExpr_isRoot(v_s_667_);
stack->m_num = v_res_670_;
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_isRoot___boxed(lean_object* v_s_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Lean_SubExpr_isRoot(v_s_671_);
lean_dec_ref(v_s_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(lean_object* v_msg_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = l_Lean_instInhabitedSubExpr_default;
v___x_676_ = lean_panic_fn_borrowed(v___x_675_, v_msg_674_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_SubExpr_bindingBody_x21___closed__2(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_679_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_680_ = lean_unsigned_to_nat(9u);
v___x_681_ = lean_unsigned_to_nat(179u);
v___x_682_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__0));
v___x_683_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_684_ = l_mkPanicMessageWithDecl(v___x_683_, v___x_682_, v___x_681_, v___x_680_, v___x_679_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingBody_x21(lean_object* v_x_685_){
_start:
{
lean_object* v_expr_686_; lean_object* v_pos_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_701_; 
v_expr_686_ = lean_ctor_get(v_x_685_, 0);
v_pos_687_ = lean_ctor_get(v_x_685_, 1);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_685_);
if (v_isSharedCheck_701_ == 0)
{
v___x_689_ = v_x_685_;
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_pos_687_);
lean_inc(v_expr_686_);
lean_dec(v_x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_701_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_b_692_; 
switch(lean_obj_tag(v_expr_686_))
{
case 7:
{
lean_object* v_body_697_; 
v_body_697_ = lean_ctor_get(v_expr_686_, 2);
lean_inc_ref(v_body_697_);
lean_dec_ref_known(v_expr_686_, 3);
v_b_692_ = v_body_697_;
goto v___jp_691_;
}
case 6:
{
lean_object* v_body_698_; 
v_body_698_ = lean_ctor_get(v_expr_686_, 2);
lean_inc_ref(v_body_698_);
lean_dec_ref_known(v_expr_686_, 3);
v_b_692_ = v_body_698_;
goto v___jp_691_;
}
default: 
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_del_object(v___x_689_);
lean_dec(v_pos_687_);
lean_dec_ref(v_expr_686_);
v___x_699_ = lean_obj_once(&l_Lean_SubExpr_bindingBody_x21___closed__2, &l_Lean_SubExpr_bindingBody_x21___closed__2_once, _init_l_Lean_SubExpr_bindingBody_x21___closed__2);
v___x_700_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_699_);
return v___x_700_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_693_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_687_);
lean_dec(v_pos_687_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_693_);
lean_ctor_set(v___x_689_, 0, v_b_692_);
v___x_695_ = v___x_689_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_b_692_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
static lean_object* _init_l_Lean_SubExpr_bindingDomain_x21___closed__1(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = ((lean_object*)(l_Lean_SubExpr_bindingBody_x21___closed__1));
v___x_704_ = lean_unsigned_to_nat(9u);
v___x_705_ = lean_unsigned_to_nat(184u);
v___x_706_ = ((lean_object*)(l_Lean_SubExpr_bindingDomain_x21___closed__0));
v___x_707_ = ((lean_object*)(l_Lean_SubExpr_Pos_head___closed__0));
v___x_708_ = l_mkPanicMessageWithDecl(v___x_707_, v___x_706_, v___x_705_, v___x_704_, v___x_703_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_bindingDomain_x21(lean_object* v_x_709_){
_start:
{
lean_object* v_expr_710_; lean_object* v_pos_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_725_; 
v_expr_710_ = lean_ctor_get(v_x_709_, 0);
v_pos_711_ = lean_ctor_get(v_x_709_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_713_ = v_x_709_;
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_pos_711_);
lean_inc(v_expr_710_);
lean_dec(v_x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_725_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_t_716_; 
switch(lean_obj_tag(v_expr_710_))
{
case 7:
{
lean_object* v_binderType_721_; 
v_binderType_721_ = lean_ctor_get(v_expr_710_, 1);
lean_inc_ref(v_binderType_721_);
lean_dec_ref_known(v_expr_710_, 3);
v_t_716_ = v_binderType_721_;
goto v___jp_715_;
}
case 6:
{
lean_object* v_binderType_722_; 
v_binderType_722_ = lean_ctor_get(v_expr_710_, 1);
lean_inc_ref(v_binderType_722_);
lean_dec_ref_known(v_expr_710_, 3);
v_t_716_ = v_binderType_722_;
goto v___jp_715_;
}
default: 
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_del_object(v___x_713_);
lean_dec(v_pos_711_);
lean_dec_ref(v_expr_710_);
v___x_723_ = lean_obj_once(&l_Lean_SubExpr_bindingDomain_x21___closed__1, &l_Lean_SubExpr_bindingDomain_x21___closed__1_once, _init_l_Lean_SubExpr_bindingDomain_x21___closed__1);
v___x_724_ = l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_723_);
return v___x_724_;
}
}
v___jp_715_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_711_);
lean_dec(v_pos_711_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v___x_717_);
lean_ctor_set(v___x_713_, 0, v_t_716_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_t_716_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonFVarId___lam__0(lean_object* v_f_726_){
_start:
{
uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = 1;
v___x_728_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_f_726_, v___x_727_);
v___x_729_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonFVarId___lam__0(lean_object* v_j_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Name_fromJson_x3f(v_j_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
v_a_743_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_734_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_734_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___impl(lean_object* v_x_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_obj_tag_nat(v_x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorIdx___impl___boxed(lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_SubExpr_GoalLocation_ctorIdx___impl(v_x_756_);
lean_dec_ref(v_x_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___redArg(lean_object* v_t_758_, lean_object* v_k_759_){
_start:
{
switch(lean_obj_tag(v_t_758_))
{
case 1:
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_a_760_);
v_a_761_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_a_761_);
lean_dec_ref_known(v_t_758_, 2);
v___x_762_ = lean_apply_2(v_k_759_, v_a_760_, v_a_761_);
return v___x_762_;
}
case 2:
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_763_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_a_763_);
v_a_764_ = lean_ctor_get(v_t_758_, 1);
lean_inc(v_a_764_);
lean_dec_ref_known(v_t_758_, 2);
v___x_765_ = lean_apply_2(v_k_759_, v_a_763_, v_a_764_);
return v___x_765_;
}
default: 
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v_t_758_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v_t_758_);
v___x_767_ = lean_apply_1(v_k_759_, v_a_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim(lean_object* v_motive_768_, lean_object* v_ctorIdx_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_k_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_770_, v_k_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_ctorElim___boxed(lean_object* v_motive_774_, lean_object* v_ctorIdx_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_SubExpr_GoalLocation_ctorElim(v_motive_774_, v_ctorIdx_775_, v_t_776_, v_h_777_, v_k_778_);
lean_dec(v_ctorIdx_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim___redArg(lean_object* v_t_780_, lean_object* v_hyp_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_780_, v_hyp_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hyp_elim(lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_hyp_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_784_, v_hyp_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim___redArg(lean_object* v_t_788_, lean_object* v_hypType_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_788_, v_hypType_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypType_elim(lean_object* v_motive_791_, lean_object* v_t_792_, lean_object* v_h_793_, lean_object* v_hypType_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_792_, v_hypType_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim___redArg(lean_object* v_t_796_, lean_object* v_hypValue_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_796_, v_hypValue_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_hypValue_elim(lean_object* v_motive_799_, lean_object* v_t_800_, lean_object* v_h_801_, lean_object* v_hypValue_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_800_, v_hypValue_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim___redArg(lean_object* v_t_804_, lean_object* v_target_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_804_, v_target_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_GoalLocation_target_elim(lean_object* v_motive_807_, lean_object* v_t_808_, lean_object* v_h_809_, lean_object* v_target_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_808_, v_target_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(lean_object* v_json_822_){
_start:
{
lean_object* v___x_823_; 
lean_inc(v_json_822_);
v___x_823_ = l_Lean_Json_getTag_x3f(v_json_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; 
lean_dec(v_json_822_);
v___x_824_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1));
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_1025_; 
v_val_825_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_827_ = v___x_823_;
v_isShared_828_ = v_isSharedCheck_1025_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_val_825_);
lean_dec(v___x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_1025_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_box(0);
v___x_830_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_831_ = lean_string_dec_eq(v_val_825_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_833_ = lean_string_dec_eq(v_val_825_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint8_t v___x_835_; 
lean_del_object(v___x_827_);
v___x_834_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_835_ = lean_string_dec_eq(v_val_825_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_837_ = lean_string_dec_eq(v_val_825_, v___x_836_);
lean_dec(v_val_825_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v_json_822_);
v___x_838_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7));
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_unsigned_to_nat(2u);
v___x_840_ = lean_box(0);
v___x_841_ = l_Lean_Json_parseCtorFields(v_json_822_, v___x_836_, v___x_839_, v___x_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v_a_850_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_841_, 1);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_array_get_borrowed(v___x_829_, v_a_850_, v___x_851_);
lean_inc(v___x_852_);
v___x_853_ = l_Lean_Name_fromJson_x3f(v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_a_850_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_a_862_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_862_);
lean_dec_ref_known(v___x_853_, 1);
v___x_863_ = lean_unsigned_to_nat(1u);
v___x_864_ = lean_array_get(v___x_829_, v_a_850_, v___x_863_);
lean_dec(v_a_850_);
v___x_865_ = l_Lean_Json_getStr_x3f(v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v_a_862_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_875_; 
v_a_874_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_874_);
lean_dec_ref_known(v___x_865_, 1);
v___x_875_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_862_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_892_; 
v_a_884_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_892_ == 0)
{
v___x_886_ = v___x_875_;
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_875_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_892_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v_a_862_);
lean_ctor_set(v___x_888_, 1, v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
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
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_val_825_);
v___x_893_ = lean_unsigned_to_nat(2u);
v___x_894_ = lean_box(0);
v___x_895_ = l_Lean_Json_parseCtorFields(v_json_822_, v___x_834_, v___x_893_, v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_a_904_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_895_, 1);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_array_get_borrowed(v___x_829_, v_a_904_, v___x_905_);
lean_inc(v___x_906_);
v___x_907_ = l_Lean_Name_fromJson_x3f(v___x_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_a_904_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v_a_916_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_907_, 1);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_array_get(v___x_829_, v_a_904_, v___x_917_);
lean_dec(v_a_904_);
v___x_919_ = l_Lean_Json_getStr_x3f(v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_a_916_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_929_; 
v_a_928_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_928_);
lean_dec_ref_known(v___x_919_, 1);
v___x_929_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_916_);
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_a_938_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_946_ == 0)
{
v___x_940_ = v___x_929_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_929_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_942_, 0, v_a_916_);
lean_ctor_set(v___x_942_, 1, v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
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
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_dec(v_val_825_);
v___x_947_ = lean_unsigned_to_nat(1u);
v___x_948_ = lean_box(0);
v___x_949_ = l_Lean_Json_parseCtorFields(v_json_822_, v___x_832_, v___x_947_, v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_del_object(v___x_827_);
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v_a_958_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_949_, 1);
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_array_get(v___x_829_, v_a_958_, v___x_959_);
lean_dec(v_a_958_);
v___x_961_ = l_Lean_Name_fromJson_x3f(v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_827_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_980_; 
v_a_970_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_980_ == 0)
{
v___x_972_ = v___x_961_;
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_961_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_980_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 0);
lean_ctor_set(v___x_827_, 0, v_a_970_);
v___x_975_ = v___x_827_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_979_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_977_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
lean_dec(v_val_825_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_box(0);
v___x_983_ = l_Lean_Json_parseCtorFields(v_json_822_, v___x_830_, v___x_981_, v___x_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_del_object(v___x_827_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_983_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v_a_992_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_983_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get(v___x_829_, v_a_992_, v___x_993_);
lean_dec(v_a_992_);
v___x_995_ = l_Lean_Json_getStr_x3f(v___x_994_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_827_);
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_995_, 1);
v___x_1005_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_1004_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_del_object(v___x_827_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1024_; 
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1024_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set_tag(v___x_827_, 3);
lean_ctor_set(v___x_827_, 0, v_a_1014_);
v___x_1019_ = v___x_827_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1019_);
v___x_1021_ = v___x_1016_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
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
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalLocation_toJson(lean_object* v_x_1028_){
_start:
{
switch(lean_obj_tag(v_x_1028_))
{
case 0:
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_a_1029_ = lean_ctor_get(v_x_1028_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v_x_1028_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v_x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3));
v___x_1034_ = 1;
v___x_1035_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1029_, v___x_1034_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set_tag(v___x_1031_, 3);
lean_ctor_set(v___x_1031_, 0, v___x_1035_);
v___x_1037_ = v___x_1031_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1033_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_Json_mkObj(v___x_1040_);
lean_dec_ref_known(v___x_1040_, 2);
return v___x_1041_;
}
}
}
case 1:
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1066_; 
v_a_1044_ = lean_ctor_get(v_x_1028_, 0);
v_a_1045_ = lean_ctor_get(v_x_1028_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1047_ = v_x_1028_;
v_isShared_1048_ = v_isSharedCheck_1066_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_inc(v_a_1044_);
lean_dec(v_x_1028_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1066_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1049_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4));
v___x_1050_ = 1;
v___x_1051_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1044_, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = l_Lean_SubExpr_Pos_toString(v_a_1045_);
lean_dec(v_a_1045_);
v___x_1054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = lean_unsigned_to_nat(2u);
v___x_1056_ = lean_mk_empty_array_with_capacity(v___x_1055_);
v___x_1057_ = lean_array_push(v___x_1056_, v___x_1052_);
v___x_1058_ = lean_array_push(v___x_1057_, v___x_1054_);
v___x_1059_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
lean_ctor_set(v___x_1047_, 1, v___x_1059_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1061_ = v___x_1047_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_Json_mkObj(v___x_1063_);
lean_dec_ref_known(v___x_1063_, 2);
return v___x_1064_;
}
}
}
case 2:
{
lean_object* v_a_1067_; lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1089_; 
v_a_1067_ = lean_ctor_get(v_x_1028_, 0);
v_a_1068_ = lean_ctor_get(v_x_1028_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1070_ = v_x_1028_;
v_isShared_1071_ = v_isSharedCheck_1089_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_dec(v_x_1028_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1089_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1072_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5));
v___x_1073_ = 1;
v___x_1074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_1067_, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
v___x_1076_ = l_Lean_SubExpr_Pos_toString(v_a_1068_);
lean_dec(v_a_1068_);
v___x_1077_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_unsigned_to_nat(2u);
v___x_1079_ = lean_mk_empty_array_with_capacity(v___x_1078_);
v___x_1080_ = lean_array_push(v___x_1079_, v___x_1075_);
v___x_1081_ = lean_array_push(v___x_1080_, v___x_1077_);
v___x_1082_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 0);
lean_ctor_set(v___x_1070_, 1, v___x_1082_);
lean_ctor_set(v___x_1070_, 0, v___x_1072_);
v___x_1084_ = v___x_1070_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_Json_mkObj(v___x_1086_);
lean_dec_ref_known(v___x_1086_, 2);
return v___x_1087_;
}
}
}
default: 
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1103_; 
v_a_1090_ = lean_ctor_get(v_x_1028_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1092_ = v_x_1028_;
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v_x_1028_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1103_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1094_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2));
v___x_1095_ = l_Lean_SubExpr_Pos_toString(v_a_1090_);
lean_dec(v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1094_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = l_Lean_Json_mkObj(v___x_1100_);
lean_dec_ref_known(v___x_1100_, 2);
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(lean_object* v_j_1106_, lean_object* v_k_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = l_Lean_Json_getObjValD(v_j_1106_, v_k_1107_);
v___x_1109_ = l_Lean_Name_fromJson_x3f(v___x_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1109_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1109_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0___boxed(lean_object* v_j_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_j_1126_, v_k_1127_);
lean_dec_ref(v_k_1127_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(lean_object* v_j_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l_Lean_Json_getObjValD(v_j_1129_, v_k_1130_);
v___x_1132_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1___boxed(lean_object* v_j_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_j_1133_, v_k_1134_);
lean_dec_ref(v_k_1134_);
return v_res_1135_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1144_ = 1;
v___x_1145_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4));
v___x_1146_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1145_, v___x_1144_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6));
v___x_1149_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5);
v___x_1150_ = lean_string_append(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = 1;
v___x_1154_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8));
v___x_1155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1154_, v___x_1153_);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1156_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9);
v___x_1157_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1158_ = lean_string_append(v___x_1157_, v___x_1156_);
return v___x_1158_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1161_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10);
v___x_1162_ = lean_string_append(v___x_1161_, v___x_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15(void){
_start:
{
uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = 1;
v___x_1167_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14));
v___x_1168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15);
v___x_1170_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7);
v___x_1171_ = lean_string_append(v___x_1170_, v___x_1169_);
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11));
v___x_1173_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16);
v___x_1174_ = lean_string_append(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson(lean_object* v_json_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
lean_inc(v_json_1175_);
v___x_1177_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_json_1175_, v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1187_; 
lean_dec(v_json_1175_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1187_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1182_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12);
v___x_1183_ = lean_string_append(v___x_1182_, v_a_1178_);
lean_dec(v_a_1178_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1183_);
v___x_1185_ = v___x_1180_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_json_1175_);
v_a_1188_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1177_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1177_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set_tag(v___x_1190_, 0);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1196_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1197_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1198_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_json_1175_, v___x_1197_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_a_1196_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1208_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = lean_obj_once(&l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17, &l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once, _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17);
v___x_1204_ = lean_string_append(v___x_1203_, v_a_1199_);
lean_dec(v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_a_1196_);
v_a_1209_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1198_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1198_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 0);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_a_1217_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v___x_1198_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1198_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1196_);
lean_ctor_set(v___x_1221_, 1, v_a_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
if (lean_obj_tag(v_a_1228_) == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_array_to_list(v_a_1229_);
return v___x_1230_;
}
else
{
lean_object* v_head_1231_; lean_object* v_tail_1232_; lean_object* v___x_1233_; 
v_head_1231_ = lean_ctor_get(v_a_1228_, 0);
lean_inc(v_head_1231_);
v_tail_1232_ = lean_ctor_get(v_a_1228_, 1);
lean_inc(v_tail_1232_);
lean_dec_ref_known(v_a_1228_, 2);
v___x_1233_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_1229_, v_head_1231_);
v_a_1228_ = v_tail_1232_;
v_a_1229_ = v___x_1233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_instToJsonGoalsLocation_toJson(lean_object* v_x_1237_){
_start:
{
lean_object* v_mvarId_1238_; lean_object* v_loc_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1261_; 
v_mvarId_1238_ = lean_ctor_get(v_x_1237_, 0);
v_loc_1239_ = lean_ctor_get(v_x_1237_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_x_1237_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1241_ = v_x_1237_;
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_loc_1239_);
lean_inc(v_mvarId_1238_);
lean_dec(v_x_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1261_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1243_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0));
v___x_1244_ = 1;
v___x_1245_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mvarId_1238_, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1246_);
lean_ctor_set(v___x_1241_, 0, v___x_1243_);
v___x_1248_ = v___x_1241_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13));
v___x_1252_ = l_Lean_SubExpr_instToJsonGoalLocation_toJson(v_loc_1239_);
v___x_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1251_);
lean_ctor_set(v___x_1253_, 1, v___x_1252_);
v___x_1254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1249_);
v___x_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___x_1254_);
lean_ctor_set(v___x_1255_, 1, v___x_1249_);
v___x_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1250_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0));
v___x_1258_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(v___x_1256_, v___x_1257_);
v___x_1259_ = l_Lean_Json_mkObj(v___x_1258_);
lean_dec(v___x_1258_);
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0(lean_object* v_p_1264_, lean_object* v_visit_1265_, lean_object* v_arg_1266_, lean_object* v_x_1267_){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_1264_);
v___x_1269_ = lean_apply_2(v_visit_1265_, v___x_1268_, v_arg_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed(lean_object* v_p_1270_, lean_object* v_visit_1271_, lean_object* v_arg_1272_, lean_object* v_x_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Expr_traverseAppWithPos___redArg___lam__0(v_p_1270_, v_visit_1271_, v_arg_1272_, v_x_1273_);
lean_dec(v_p_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object* v_inst_1275_, lean_object* v_visit_1276_, lean_object* v_p_1277_, lean_object* v_e_1278_){
_start:
{
if (lean_obj_tag(v_e_1278_) == 5)
{
lean_object* v_toApplicative_1279_; lean_object* v_toFunctor_1280_; lean_object* v_toSeq_1281_; lean_object* v_fn_1282_; lean_object* v_arg_1283_; lean_object* v_map_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v_toApplicative_1279_ = lean_ctor_get(v_inst_1275_, 0);
v_toFunctor_1280_ = lean_ctor_get(v_toApplicative_1279_, 0);
v_toSeq_1281_ = lean_ctor_get(v_toApplicative_1279_, 2);
lean_inc(v_toSeq_1281_);
v_fn_1282_ = lean_ctor_get(v_e_1278_, 0);
lean_inc_ref(v_fn_1282_);
v_arg_1283_ = lean_ctor_get(v_e_1278_, 1);
v_map_1284_ = lean_ctor_get(v_toFunctor_1280_, 0);
lean_inc(v_map_1284_);
lean_inc_ref(v_arg_1283_);
lean_inc(v_visit_1276_);
lean_inc(v_p_1277_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1285_, 0, v_p_1277_);
lean_closure_set(v___f_1285_, 1, v_visit_1276_);
lean_closure_set(v___f_1285_, 2, v_arg_1283_);
v___x_1286_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed), 3, 1);
lean_closure_set(v___x_1286_, 0, v_e_1278_);
v___x_1287_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_1277_);
lean_dec(v_p_1277_);
v___x_1288_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1275_, v_visit_1276_, v___x_1287_, v_fn_1282_);
v___x_1289_ = lean_apply_4(v_map_1284_, lean_box(0), lean_box(0), v___x_1286_, v___x_1288_);
v___x_1290_ = lean_apply_4(v_toSeq_1281_, lean_box(0), lean_box(0), v___x_1289_, v___f_1285_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; 
lean_dec_ref(v_inst_1275_);
v___x_1291_ = lean_apply_2(v_visit_1276_, v_p_1277_, v_e_1278_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseAppWithPos(lean_object* v_M_1292_, lean_object* v_inst_1293_, lean_object* v_visit_1294_, lean_object* v_p_1295_, lean_object* v_e_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_1293_, v_visit_1294_, v_p_1295_, v_e_1296_);
return v___x_1297_;
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
