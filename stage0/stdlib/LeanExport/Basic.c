// Lean compiler output
// Module: LeanExport.Basic
// Imports: public import Lean public import Std.Data.HashMap.Basic
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
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_setObjVal_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Level_param___override(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_instReprDataValue_repr(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_instInhabitedConstantInfo_default;
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
extern lean_object* l_Lean_githash;
extern lean_object* l_Lean_versionString;
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_println___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "implicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "strictImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instImplicit"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unsafe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__0_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "safe"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__2_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__4_value)}};
static const lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__0;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__1;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__2;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__3;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__4;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__5;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__6;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__7;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__8;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__9;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__10;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__11;
static lean_once_cell_t l_LeanExport_M_run___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_M_run___redArg___closed__12;
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--ignore-missing"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__2___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "--export-mdata"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__0___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_any___at___00LeanExport_initState_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--export-unsafe"};
static const lean_object* l_List_any___at___00LeanExport_initState_spec__1___closed__0 = (const lean_object*)&l_List_any___at___00LeanExport_initState_spec__1___closed__0_value;
LEAN_EXPORT uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object*);
static const lean_closure_object l_LeanExport_initState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_LeanExport_initState___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_LeanExport_initState___closed__0 = (const lean_object*)&l_LeanExport_initState___closed__0_value;
LEAN_EXPORT lean_object* l_LeanExport_initState(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LeanExport.Basic"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpName"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pre"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "il"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "max"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "imax"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "param"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.LeanExport.Basic.0.LeanExport.dumpLevel"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "_private.LeanExport.Basic.0.LeanExport.removeMData"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "LeanExport.dumpConstant"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 135, .m_capacity = 135, .m_length = 134, .m_data = "assertion violation: ((!ctorVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1873.0 ).exportUnsafe)\n          "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Expected a `ConstantInfo.ctorInfo`."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "assertion violation: ((!recVal.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.2114.0 ).exportUnsafe)\n        "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "expected a `constantinfo.recinfo`."};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_LeanExport_dumpExpr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__0;
static lean_once_cell_t l_LeanExport_dumpExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExpr___closed__1;
static const lean_string_object l_LeanExport_dumpExprAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ie"};
static const lean_object* l_LeanExport_dumpExprAux___closed__0 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bvar"};
static const lean_object* l_LeanExport_dumpExprAux___closed__1 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__1_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_LeanExport_dumpExprAux___closed__2 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__2_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_LeanExport_dumpExprAux___closed__3 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "us"};
static const lean_object* l_LeanExport_dumpExprAux___closed__4 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__4_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_LeanExport_dumpExprAux___closed__5 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__5_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "fn"};
static const lean_object* l_LeanExport_dumpExprAux___closed__6 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__6_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_LeanExport_dumpExprAux___closed__7 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__7_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lam"};
static const lean_object* l_LeanExport_dumpExprAux___closed__8 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__8_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "body"};
static const lean_object* l_LeanExport_dumpExprAux___closed__9 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__9_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "binderInfo"};
static const lean_object* l_LeanExport_dumpExprAux___closed__10 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__10_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "forallE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__11 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__11_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "letE"};
static const lean_object* l_LeanExport_dumpExprAux___closed__12 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__12_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_LeanExport_dumpExprAux___closed__13 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__13_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nondep"};
static const lean_object* l_LeanExport_dumpExprAux___closed__14 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__14_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__15 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__15_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__1_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__4_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpExprAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_LeanExport_dumpExprAux___closed__16 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__16_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mdata"};
static const lean_object* l_LeanExport_dumpExprAux___closed__17 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__17_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_LeanExport_dumpExprAux___closed__18 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__18_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "expr"};
static const lean_object* l_LeanExport_dumpExprAux___closed__19 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__19_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_LeanExport_dumpExprAux___closed__20 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__20_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeName"};
static const lean_object* l_LeanExport_dumpExprAux___closed__21 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__21_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "idx"};
static const lean_object* l_LeanExport_dumpExprAux___closed__22 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__22_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "struct"};
static const lean_object* l_LeanExport_dumpExprAux___closed__23 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__23_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "cannot export free variables or metavariables"};
static const lean_object* l_LeanExport_dumpExprAux___closed__25 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__25_value;
static const lean_string_object l_LeanExport_dumpExprAux___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanExport.dumpExprAux"};
static const lean_object* l_LeanExport_dumpExprAux___closed__24 = (const lean_object*)&l_LeanExport_dumpExprAux___closed__24_value;
static lean_once_cell_t l_LeanExport_dumpExprAux___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpExprAux___closed__26;
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "levelParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numIndices"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numNested"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isRec"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "isReflexive"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "isUnsafe"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "induct"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cidx"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numFields"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nfields"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1_value;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "numMotives"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numMinors"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "rules"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "k"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t, size_t, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_LeanExport_dumpConstant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l_LeanExport_dumpConstant___closed__0 = (const lean_object*)&l_LeanExport_dumpConstant___closed__0_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "types"};
static const lean_object* l_LeanExport_dumpConstant___closed__1 = (const lean_object*)&l_LeanExport_dumpConstant___closed__1_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "recs"};
static const lean_object* l_LeanExport_dumpConstant___closed__2 = (const lean_object*)&l_LeanExport_dumpConstant___closed__2_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l_LeanExport_dumpConstant___closed__3 = (const lean_object*)&l_LeanExport_dumpConstant___closed__3_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_LeanExport_dumpConstant___closed__4 = (const lean_object*)&l_LeanExport_dumpConstant___closed__4_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hints"};
static const lean_object* l_LeanExport_dumpConstant___closed__5 = (const lean_object*)&l_LeanExport_dumpConstant___closed__5_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "safety"};
static const lean_object* l_LeanExport_dumpConstant___closed__6 = (const lean_object*)&l_LeanExport_dumpConstant___closed__6_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_LeanExport_dumpConstant___closed__7 = (const lean_object*)&l_LeanExport_dumpConstant___closed__7_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_LeanExport_dumpConstant___closed__8 = (const lean_object*)&l_LeanExport_dumpConstant___closed__8_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__8_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_LeanExport_dumpConstant___closed__9 = (const lean_object*)&l_LeanExport_dumpConstant___closed__9_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_LeanExport_dumpConstant___closed__10 = (const lean_object*)&l_LeanExport_dumpConstant___closed__10_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_LeanExport_dumpConstant___closed__15 = (const lean_object*)&l_LeanExport_dumpConstant___closed__15_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_LeanExport_dumpConstant___closed__16 = (const lean_object*)&l_LeanExport_dumpConstant___closed__16_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value_aux_0),((lean_object*)&l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_LeanExport_dumpConstant___closed__14 = (const lean_object*)&l_LeanExport_dumpConstant___closed__14_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__14_value),((lean_object*)&l_LeanExport_dumpConstant___closed__16_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__17 = (const lean_object*)&l_LeanExport_dumpConstant___closed__17_value;
static const lean_string_object l_LeanExport_dumpConstant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_LeanExport_dumpConstant___closed__12 = (const lean_object*)&l_LeanExport_dumpConstant___closed__12_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_LeanExport_dumpConstant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value_aux_0),((lean_object*)&l_LeanExport_dumpConstant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_LeanExport_dumpConstant___closed__13 = (const lean_object*)&l_LeanExport_dumpConstant___closed__13_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__13_value),((lean_object*)&l_LeanExport_dumpConstant___closed__17_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__18 = (const lean_object*)&l_LeanExport_dumpConstant___closed__18_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_LeanExport_dumpConstant___closed__10_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_LeanExport_dumpConstant___closed__11 = (const lean_object*)&l_LeanExport_dumpConstant___closed__11_value;
static const lean_ctor_object l_LeanExport_dumpConstant___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_LeanExport_dumpConstant___closed__11_value),((lean_object*)&l_LeanExport_dumpConstant___closed__18_value)}};
static const lean_object* l_LeanExport_dumpConstant___closed__19 = (const lean_object*)&l_LeanExport_dumpConstant___closed__19_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Constant "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " not found in environment."};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_LeanExport_dumpConstant___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_LeanExport_dumpConstant___closed__20 = (const lean_object*)&l_LeanExport_dumpConstant___closed__20_value;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__21;
static lean_once_cell_t l_LeanExport_dumpConstant___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpConstant___closed__22;
static const lean_closure_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 367, .m_capacity = 367, .m_length = 366, .m_data = "assertion violation: ctorVals.size == 0\n\n    /- We dump the constructor dependencies (which will not include the inductives in this block since we've\n    added the names to `visitedConstants`) before actually outputting anything in this inductive block to\n    ensure e.g. the `LT` in `Fin.mk` is dumped before this inductive block appears in the export file. -/\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2;
static const lean_string_object l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 127, .m_capacity = 127, .m_length = 126, .m_data = "assertion violation: ((!val.isUnsafe) || ( __do_lift._@.LeanExport.Basic.2173241011._hygCtx._hyg.1797.0 ).exportUnsafe)\n      "};
static const lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "version"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "githash"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lean4export"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__9_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__10_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "3.1.0"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__12_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__13_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value;
static const lean_ctor_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__11_value),((lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15_value)}};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19_value;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "exporter"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23;
static const lean_string_object l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "format"};
static const lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24 = (const lean_object*)&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24_value;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31;
static lean_once_cell_t l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32;
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
static lean_once_cell_t l_LeanExport_dumpMetadata___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_LeanExport_dumpMetadata___redArg___closed__0;
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg(lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__1));
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__3));
return v___x_15_;
}
case 2:
{
lean_object* v___x_16_; 
v___x_16_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__5));
return v___x_16_;
}
default: 
{
lean_object* v___x_17_; 
v___x_17_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___closed__7));
return v___x_17_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_13_ = stack[0].m_num;
lean_object* v_res_18_;
v_res_18_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_x_13_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson___boxed(lean_object* v_x_19_){
_start:
{
uint8_t v_x_64__boxed_20_; lean_object* v_res_21_; 
v_x_64__boxed_20_ = lean_unbox(v_x_19_);
v_res_21_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_x_64__boxed_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(lean_object* v_x_29_){
_start:
{
switch(lean_obj_tag(v_x_29_))
{
case 0:
{
lean_object* v___x_30_; 
v___x_30_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__1));
return v___x_30_;
}
case 1:
{
lean_object* v___x_31_; 
v___x_31_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__3));
return v___x_31_;
}
default: 
{
uint32_t v_a_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_a_32_ = lean_ctor_get_uint32(v_x_29_, 0);
v___x_33_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__4));
v___x_34_ = lean_uint32_to_nat(v_a_32_);
v___x_35_ = l_Lean_JsonNumber_fromNat(v___x_34_);
v___x_36_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = l_Lean_Json_mkObj(v___x_39_);
lean_dec_ref_known(v___x_39_, 2);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___boxed(lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_x_41_);
lean_dec(v_x_41_);
return v_res_42_;
}
}
lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(uint8_t v_x_55_){
_start:
{
switch(v_x_55_)
{
case 0:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__1));
return v___x_56_;
}
case 1:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__3));
return v___x_57_;
}
case 2:
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__5));
return v___x_58_;
}
default: 
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__7));
return v___x_59_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__Lean_QuotKind_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_55_ = stack[0].m_num;
lean_object* v_res_60_;
v_res_60_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_x_55_);
stack->m_obj
 = v_res_60_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___boxed(lean_object* v_x_61_){
_start:
{
uint8_t v_x_64__boxed_62_; lean_object* v_res_63_; 
v_x_64__boxed_62_ = lean_unbox(v_x_61_);
v_res_63_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_x_64__boxed_62_);
return v_res_63_;
}
}
lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(uint8_t v_x_73_){
_start:
{
switch(v_x_73_)
{
case 0:
{
lean_object* v___x_74_; 
v___x_74_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__1));
return v___x_74_;
}
case 1:
{
lean_object* v___x_75_; 
v___x_75_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__3));
return v___x_75_;
}
default: 
{
lean_object* v___x_76_; 
v___x_76_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___closed__5));
return v___x_76_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_73_ = stack[0].m_num;
lean_object* v_res_77_;
v_res_77_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_x_73_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson___boxed(lean_object* v_x_78_){
_start:
{
uint8_t v_x_49__boxed_79_; lean_object* v_res_80_; 
v_x_49__boxed_79_ = lean_unbox(v_x_78_);
v_res_80_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_x_49__boxed_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
if (lean_obj_tag(v_a_81_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = l_List_reverse___redArg(v_a_82_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_109_; 
v_head_84_ = lean_ctor_get(v_a_81_, 0);
v_tail_85_ = lean_ctor_get(v_a_81_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_a_81_);
if (v_isSharedCheck_109_ == 0)
{
v___x_87_ = v_a_81_;
v_isShared_88_ = v_isSharedCheck_109_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_tail_85_);
lean_inc(v_head_84_);
lean_dec(v_a_81_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_109_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_fst_89_; lean_object* v_snd_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_108_; 
v_fst_89_ = lean_ctor_get(v_head_84_, 0);
v_snd_90_ = lean_ctor_get(v_head_84_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_head_84_);
if (v_isSharedCheck_108_ == 0)
{
v___x_92_ = v_head_84_;
v_isShared_93_ = v_isSharedCheck_108_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_snd_90_);
lean_inc(v_fst_89_);
lean_dec(v_head_84_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_108_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_94_ = 1;
v___x_95_ = l_Lean_Name_toString(v_fst_89_, v___x_94_);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = l_Lean_instReprDataValue_repr(v_snd_90_, v___x_96_);
v___x_98_ = l_Std_Format_defWidth;
v___x_99_ = l_Std_Format_pretty(v___x_97_, v___x_98_, v___x_96_, v___x_96_);
v___x_100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___x_100_);
lean_ctor_set(v___x_92_, 0, v___x_95_);
v___x_102_ = v___x_92_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_100_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_104_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 1, v_a_82_);
lean_ctor_set(v___x_87_, 0, v___x_102_);
v___x_104_ = v___x_87_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v_a_82_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
v_a_81_ = v_tail_85_;
v_a_82_ = v___x_104_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__Lean_KVMap_toJson(lean_object* v_kvs_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_box(0);
v___x_112_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__Lean_KVMap_toJson_spec__0(v_kvs_110_, v___x_111_);
v___x_113_ = l_Lean_Json_mkObj(v___x_112_);
lean_dec(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(lean_object* v_a_114_, lean_object* v_b_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_dec(v_b_115_);
lean_dec(v_a_114_);
return v_x_116_;
}
else
{
lean_object* v_key_117_; lean_object* v_value_118_; lean_object* v_tail_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_131_; 
v_key_117_ = lean_ctor_get(v_x_116_, 0);
v_value_118_ = lean_ctor_get(v_x_116_, 1);
v_tail_119_ = lean_ctor_get(v_x_116_, 2);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_116_);
if (v_isSharedCheck_131_ == 0)
{
v___x_121_ = v_x_116_;
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_tail_119_);
lean_inc(v_value_118_);
lean_inc(v_key_117_);
lean_dec(v_x_116_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_131_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = lean_name_eq(v_key_117_, v_a_114_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_114_, v_b_115_, v_tail_119_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 2, v___x_124_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_key_117_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_value_118_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v_value_118_);
lean_dec(v_key_117_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 1, v_b_115_);
lean_ctor_set(v___x_121_, 0, v_a_114_);
v___x_129_ = v___x_121_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_114_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_b_115_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_tail_119_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_132_, lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
return v_x_132_;
}
else
{
lean_object* v_key_134_; lean_object* v_value_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_162_; 
v_key_134_ = lean_ctor_get(v_x_133_, 0);
v_value_135_ = lean_ctor_get(v_x_133_, 1);
v_tail_136_ = lean_ctor_get(v_x_133_, 2);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_162_ == 0)
{
v___x_138_ = v_x_133_;
v_isShared_139_ = v_isSharedCheck_162_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_value_135_);
lean_inc(v_key_134_);
lean_dec(v_x_133_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_162_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; uint64_t v___y_142_; 
v___x_140_ = lean_array_get_size(v_x_132_);
if (lean_obj_tag(v_key_134_) == 0)
{
uint64_t v___x_160_; 
v___x_160_ = 1723ULL;
v___y_142_ = v___x_160_;
goto v___jp_141_;
}
else
{
uint64_t v_hash_161_; 
v_hash_161_ = lean_ctor_get_uint64(v_key_134_, sizeof(void*)*2);
v___y_142_ = v_hash_161_;
goto v___jp_141_;
}
v___jp_141_:
{
uint64_t v___x_143_; uint64_t v___x_144_; uint64_t v_fold_145_; uint64_t v___x_146_; uint64_t v___x_147_; uint64_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; size_t v___x_152_; size_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_143_ = 32ULL;
v___x_144_ = lean_uint64_shift_right(v___y_142_, v___x_143_);
v_fold_145_ = lean_uint64_xor(v___y_142_, v___x_144_);
v___x_146_ = 16ULL;
v___x_147_ = lean_uint64_shift_right(v_fold_145_, v___x_146_);
v___x_148_ = lean_uint64_xor(v_fold_145_, v___x_147_);
v___x_149_ = lean_uint64_to_usize(v___x_148_);
v___x_150_ = lean_usize_of_nat(v___x_140_);
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_sub(v___x_150_, v___x_151_);
v___x_153_ = lean_usize_land(v___x_149_, v___x_152_);
v___x_154_ = lean_array_uget_borrowed(v_x_132_, v___x_153_);
lean_inc(v___x_154_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 2, v___x_154_);
v___x_156_ = v___x_138_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_key_134_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_value_135_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v___x_154_);
v___x_156_ = v_reuseFailAlloc_159_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_array_uset(v_x_132_, v___x_153_, v___x_156_);
v_x_132_ = v___x_157_;
v_x_133_ = v_tail_136_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(lean_object* v_i_163_, lean_object* v_source_164_, lean_object* v_target_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = lean_array_get_size(v_source_164_);
v___x_167_ = lean_nat_dec_lt(v_i_163_, v___x_166_);
if (v___x_167_ == 0)
{
lean_dec_ref(v_source_164_);
lean_dec(v_i_163_);
return v_target_165_;
}
else
{
lean_object* v_es_168_; lean_object* v___x_169_; lean_object* v_source_170_; lean_object* v_target_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_es_168_ = lean_array_fget(v_source_164_, v_i_163_);
v___x_169_ = lean_box(0);
v_source_170_ = lean_array_fset(v_source_164_, v_i_163_, v___x_169_);
v_target_171_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_target_165_, v_es_168_);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = lean_nat_add(v_i_163_, v___x_172_);
lean_dec(v_i_163_);
v_i_163_ = v___x_173_;
v_source_164_ = v_source_170_;
v_target_165_ = v_target_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(lean_object* v_data_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_nbuckets_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_176_ = lean_array_get_size(v_data_175_);
v___x_177_ = lean_unsigned_to_nat(2u);
v_nbuckets_178_ = lean_nat_mul(v___x_176_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = lean_box(0);
v___x_181_ = lean_mk_array(v_nbuckets_178_, v___x_180_);
v___x_182_ = lean_array_propagate_mark(v_data_175_, v___x_181_);
v___x_183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v___x_179_, v_data_175_, v___x_182_);
return v___x_183_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(lean_object* v_a_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_185_) == 0)
{
uint8_t v___x_186_; 
v___x_186_ = 0;
return v___x_186_;
}
else
{
lean_object* v_key_187_; lean_object* v_tail_188_; uint8_t v___x_189_; 
v_key_187_ = lean_ctor_get(v_x_185_, 0);
v_tail_188_ = lean_ctor_get(v_x_185_, 2);
v___x_189_ = lean_name_eq(v_key_187_, v_a_184_);
if (v___x_189_ == 0)
{
v_x_185_ = v_tail_188_;
goto _start;
}
else
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_184_ = stack[0].m_obj;
lean_object* v_x_185_ = stack[1].m_obj;
uint8_t v_res_191_;
v_res_191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_184_, v_x_185_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg___boxed(lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_192_, v_x_193_);
lean_dec(v_x_193_);
lean_dec(v_a_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v_size_199_; lean_object* v_buckets_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_246_; 
v_size_199_ = lean_ctor_get(v_m_196_, 0);
v_buckets_200_ = lean_ctor_get(v_m_196_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_m_196_);
if (v_isSharedCheck_246_ == 0)
{
v___x_202_ = v_m_196_;
v_isShared_203_ = v_isSharedCheck_246_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_buckets_200_);
lean_inc(v_size_199_);
lean_dec(v_m_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_246_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; uint64_t v___y_206_; 
v___x_204_ = lean_array_get_size(v_buckets_200_);
if (lean_obj_tag(v_a_197_) == 0)
{
uint64_t v___x_244_; 
v___x_244_ = 1723ULL;
v___y_206_ = v___x_244_;
goto v___jp_205_;
}
else
{
uint64_t v_hash_245_; 
v_hash_245_ = lean_ctor_get_uint64(v_a_197_, sizeof(void*)*2);
v___y_206_ = v_hash_245_;
goto v___jp_205_;
}
v___jp_205_:
{
uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v_fold_209_; uint64_t v___x_210_; uint64_t v___x_211_; uint64_t v___x_212_; size_t v___x_213_; size_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; lean_object* v_bkt_218_; uint8_t v___x_219_; 
v___x_207_ = 32ULL;
v___x_208_ = lean_uint64_shift_right(v___y_206_, v___x_207_);
v_fold_209_ = lean_uint64_xor(v___y_206_, v___x_208_);
v___x_210_ = 16ULL;
v___x_211_ = lean_uint64_shift_right(v_fold_209_, v___x_210_);
v___x_212_ = lean_uint64_xor(v_fold_209_, v___x_211_);
v___x_213_ = lean_uint64_to_usize(v___x_212_);
v___x_214_ = lean_usize_of_nat(v___x_204_);
v___x_215_ = ((size_t)1ULL);
v___x_216_ = lean_usize_sub(v___x_214_, v___x_215_);
v___x_217_ = lean_usize_land(v___x_213_, v___x_216_);
v_bkt_218_ = lean_array_uget_borrowed(v_buckets_200_, v___x_217_);
v___x_219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_197_, v_bkt_218_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v_size_x27_221_; lean_object* v___x_222_; lean_object* v_buckets_x27_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v___x_220_ = lean_unsigned_to_nat(1u);
v_size_x27_221_ = lean_nat_add(v_size_199_, v___x_220_);
lean_dec(v_size_199_);
lean_inc(v_bkt_218_);
v___x_222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_222_, 0, v_a_197_);
lean_ctor_set(v___x_222_, 1, v_b_198_);
lean_ctor_set(v___x_222_, 2, v_bkt_218_);
v_buckets_x27_223_ = lean_array_uset(v_buckets_200_, v___x_217_, v___x_222_);
v___x_224_ = lean_unsigned_to_nat(4u);
v___x_225_ = lean_nat_mul(v_size_x27_221_, v___x_224_);
v___x_226_ = lean_unsigned_to_nat(3u);
v___x_227_ = lean_nat_div(v___x_225_, v___x_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_array_get_size(v_buckets_x27_223_);
v___x_229_ = lean_nat_dec_le(v___x_227_, v___x_228_);
lean_dec(v___x_227_);
if (v___x_229_ == 0)
{
lean_object* v_val_230_; lean_object* v___x_232_; 
v_val_230_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_buckets_x27_223_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_val_230_);
lean_ctor_set(v___x_202_, 0, v_size_x27_221_);
v___x_232_ = v___x_202_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_size_x27_221_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_val_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
else
{
lean_object* v___x_235_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_buckets_x27_223_);
lean_ctor_set(v___x_202_, 0, v_size_x27_221_);
v___x_235_ = v___x_202_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_size_x27_221_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_buckets_x27_223_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v___x_237_; lean_object* v_buckets_x27_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
lean_inc(v_bkt_218_);
v___x_237_ = lean_box(0);
v_buckets_x27_238_ = lean_array_uset(v_buckets_200_, v___x_217_, v___x_237_);
v___x_239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_197_, v_b_198_, v_bkt_218_);
v___x_240_ = lean_array_uset(v_buckets_x27_238_, v___x_217_, v___x_239_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v___x_240_);
v___x_242_ = v___x_202_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_size_199_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(lean_object* v_a_247_, lean_object* v_b_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_dec(v_b_248_);
lean_dec(v_a_247_);
return v_x_249_;
}
else
{
lean_object* v_key_250_; lean_object* v_value_251_; lean_object* v_tail_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_264_; 
v_key_250_ = lean_ctor_get(v_x_249_, 0);
v_value_251_ = lean_ctor_get(v_x_249_, 1);
v_tail_252_ = lean_ctor_get(v_x_249_, 2);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_264_ == 0)
{
v___x_254_ = v_x_249_;
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_tail_252_);
lean_inc(v_value_251_);
lean_inc(v_key_250_);
lean_dec(v_x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_264_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_level_eq(v_key_250_, v_a_247_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_247_, v_b_248_, v_tail_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 2, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_key_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_value_251_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v_value_251_);
lean_dec(v_key_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_b_248_);
lean_ctor_set(v___x_254_, 0, v_a_247_);
v___x_262_ = v___x_254_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_247_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_b_248_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_tail_252_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
return v_x_265_;
}
else
{
lean_object* v_key_267_; lean_object* v_value_268_; lean_object* v_tail_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_292_; 
v_key_267_ = lean_ctor_get(v_x_266_, 0);
v_value_268_ = lean_ctor_get(v_x_266_, 1);
v_tail_269_ = lean_ctor_get(v_x_266_, 2);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_266_);
if (v_isSharedCheck_292_ == 0)
{
v___x_271_ = v_x_266_;
v_isShared_272_ = v_isSharedCheck_292_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_tail_269_);
lean_inc(v_value_268_);
lean_inc(v_key_267_);
lean_dec(v_x_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_292_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v_fold_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_273_ = lean_array_get_size(v_x_265_);
v___x_274_ = l_Lean_Level_hash(v_key_267_);
v___x_275_ = 32ULL;
v___x_276_ = lean_uint64_shift_right(v___x_274_, v___x_275_);
v_fold_277_ = lean_uint64_xor(v___x_274_, v___x_276_);
v___x_278_ = 16ULL;
v___x_279_ = lean_uint64_shift_right(v_fold_277_, v___x_278_);
v___x_280_ = lean_uint64_xor(v_fold_277_, v___x_279_);
v___x_281_ = lean_uint64_to_usize(v___x_280_);
v___x_282_ = lean_usize_of_nat(v___x_273_);
v___x_283_ = ((size_t)1ULL);
v___x_284_ = lean_usize_sub(v___x_282_, v___x_283_);
v___x_285_ = lean_usize_land(v___x_281_, v___x_284_);
v___x_286_ = lean_array_uget_borrowed(v_x_265_, v___x_285_);
lean_inc(v___x_286_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 2, v___x_286_);
v___x_288_ = v___x_271_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_key_267_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_value_268_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v___x_286_);
v___x_288_ = v_reuseFailAlloc_291_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; 
v___x_289_ = lean_array_uset(v_x_265_, v___x_285_, v___x_288_);
v_x_265_ = v___x_289_;
v_x_266_ = v_tail_269_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(lean_object* v_i_293_, lean_object* v_source_294_, lean_object* v_target_295_){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = lean_array_get_size(v_source_294_);
v___x_297_ = lean_nat_dec_lt(v_i_293_, v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_source_294_);
lean_dec(v_i_293_);
return v_target_295_;
}
else
{
lean_object* v_es_298_; lean_object* v___x_299_; lean_object* v_source_300_; lean_object* v_target_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_es_298_ = lean_array_fget(v_source_294_, v_i_293_);
v___x_299_ = lean_box(0);
v_source_300_ = lean_array_fset(v_source_294_, v_i_293_, v___x_299_);
v_target_301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_target_295_, v_es_298_);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_i_293_, v___x_302_);
lean_dec(v_i_293_);
v_i_293_ = v___x_303_;
v_source_294_ = v_source_300_;
v_target_295_ = v_target_301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(lean_object* v_data_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_nbuckets_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_306_ = lean_array_get_size(v_data_305_);
v___x_307_ = lean_unsigned_to_nat(2u);
v_nbuckets_308_ = lean_nat_mul(v___x_306_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_box(0);
v___x_311_ = lean_mk_array(v_nbuckets_308_, v___x_310_);
v___x_312_ = lean_array_propagate_mark(v_data_305_, v___x_311_);
v___x_313_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v___x_309_, v_data_305_, v___x_312_);
return v___x_313_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(lean_object* v_a_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 0;
return v___x_316_;
}
else
{
lean_object* v_key_317_; lean_object* v_tail_318_; uint8_t v___x_319_; 
v_key_317_ = lean_ctor_get(v_x_315_, 0);
v_tail_318_ = lean_ctor_get(v_x_315_, 2);
v___x_319_ = lean_level_eq(v_key_317_, v_a_314_);
if (v___x_319_ == 0)
{
v_x_315_ = v_tail_318_;
goto _start;
}
else
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_314_ = stack[0].m_obj;
lean_object* v_x_315_ = stack[1].m_obj;
uint8_t v_res_321_;
v_res_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_314_, v_x_315_);
stack->m_num = v_res_321_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg___boxed(lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec(v_a_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(lean_object* v_m_326_, lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
lean_object* v_size_329_; lean_object* v_buckets_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_373_; 
v_size_329_ = lean_ctor_get(v_m_326_, 0);
v_buckets_330_ = lean_ctor_get(v_m_326_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_m_326_);
if (v_isSharedCheck_373_ == 0)
{
v___x_332_ = v_m_326_;
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_buckets_330_);
lean_inc(v_size_329_);
lean_dec(v_m_326_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_373_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v_fold_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; lean_object* v_bkt_347_; uint8_t v___x_348_; 
v___x_334_ = lean_array_get_size(v_buckets_330_);
v___x_335_ = l_Lean_Level_hash(v_a_327_);
v___x_336_ = 32ULL;
v___x_337_ = lean_uint64_shift_right(v___x_335_, v___x_336_);
v_fold_338_ = lean_uint64_xor(v___x_335_, v___x_337_);
v___x_339_ = 16ULL;
v___x_340_ = lean_uint64_shift_right(v_fold_338_, v___x_339_);
v___x_341_ = lean_uint64_xor(v_fold_338_, v___x_340_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = lean_usize_of_nat(v___x_334_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = lean_usize_sub(v___x_343_, v___x_344_);
v___x_346_ = lean_usize_land(v___x_342_, v___x_345_);
v_bkt_347_ = lean_array_uget_borrowed(v_buckets_330_, v___x_346_);
v___x_348_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_327_, v_bkt_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_size_x27_350_; lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_349_ = lean_unsigned_to_nat(1u);
v_size_x27_350_ = lean_nat_add(v_size_329_, v___x_349_);
lean_dec(v_size_329_);
lean_inc(v_bkt_347_);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v_a_327_);
lean_ctor_set(v___x_351_, 1, v_b_328_);
lean_ctor_set(v___x_351_, 2, v_bkt_347_);
v_buckets_x27_352_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v_size_x27_350_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_div(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_array_get_size(v_buckets_x27_352_);
v___x_358_ = lean_nat_dec_le(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
if (v___x_358_ == 0)
{
lean_object* v_val_359_; lean_object* v___x_361_; 
v_val_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_buckets_x27_352_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_val_359_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_361_ = v___x_332_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_buckets_x27_352_);
lean_ctor_set(v___x_332_, 0, v_size_x27_350_);
v___x_364_ = v___x_332_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_buckets_x27_352_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
else
{
lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_inc(v_bkt_347_);
v___x_366_ = lean_box(0);
v_buckets_x27_367_ = lean_array_uset(v_buckets_330_, v___x_346_, v___x_366_);
v___x_368_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_327_, v_b_328_, v_bkt_347_);
v___x_369_ = lean_array_uset(v_buckets_x27_367_, v___x_346_, v___x_368_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_369_);
v___x_371_ = v___x_332_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_size_329_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_374_ = lean_box(0);
v___x_375_ = lean_unsigned_to_nat(524288u);
v___x_376_ = lean_mk_array(v___x_375_, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__0, &l_LeanExport_M_run___redArg___closed__0_once, _init_l_LeanExport_M_run___redArg___closed__0);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_box(0);
v___x_382_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__1, &l_LeanExport_M_run___redArg___closed__1_once, _init_l_LeanExport_M_run___redArg___closed__1);
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v___x_382_, v___x_381_, v___x_380_);
return v___x_383_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_box(0);
v___x_385_ = lean_unsigned_to_nat(2048u);
v___x_386_ = lean_mk_array(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__3, &l_LeanExport_M_run___redArg___closed__3_once, _init_l_LeanExport_M_run___redArg___closed__3);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__5(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_box(0);
v___x_392_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__4, &l_LeanExport_M_run___redArg___closed__4_once, _init_l_LeanExport_M_run___redArg___closed__4);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v___x_392_, v___x_391_, v___x_390_);
return v___x_393_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__6(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_unsigned_to_nat(16777216u);
v___x_396_ = lean_mk_array(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__7(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__6, &l_LeanExport_M_run___redArg___closed__6_once, _init_l_LeanExport_M_run___redArg___closed__6);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__8(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = lean_box(0);
v___x_401_ = lean_unsigned_to_nat(16u);
v___x_402_ = lean_mk_array(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__9(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__8, &l_LeanExport_M_run___redArg___closed__8_once, _init_l_LeanExport_M_run___redArg___closed__8);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
return v___x_405_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__10(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
v___x_407_ = lean_unsigned_to_nat(262144u);
v___x_408_ = lean_mk_array(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__11(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__10, &l_LeanExport_M_run___redArg___closed__10_once, _init_l_LeanExport_M_run___redArg___closed__10);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_LeanExport_M_run___redArg___closed__12(void){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_412_ = lean_box(1);
v___x_413_ = 0;
v___x_414_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__11, &l_LeanExport_M_run___redArg___closed__11_once, _init_l_LeanExport_M_run___redArg___closed__11);
v___x_415_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__9, &l_LeanExport_M_run___redArg___closed__9_once, _init_l_LeanExport_M_run___redArg___closed__9);
v___x_416_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__7, &l_LeanExport_M_run___redArg___closed__7_once, _init_l_LeanExport_M_run___redArg___closed__7);
v___x_417_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__5, &l_LeanExport_M_run___redArg___closed__5_once, _init_l_LeanExport_M_run___redArg___closed__5);
v___x_418_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__2, &l_LeanExport_M_run___redArg___closed__2_once, _init_l_LeanExport_M_run___redArg___closed__2);
v___x_419_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_417_);
lean_ctor_set(v___x_419_, 2, v___x_416_);
lean_ctor_set(v___x_419_, 3, v___x_415_);
lean_ctor_set(v___x_419_, 4, v___x_414_);
lean_ctor_set(v___x_419_, 5, v___x_412_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*6, v___x_413_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*6 + 1, v___x_413_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*6 + 2, v___x_413_);
return v___x_419_;
}
}
lean_object* l_LeanExport_M_run___redArg(lean_object* v_env_420_, lean_object* v_act_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_LeanExport_M_run___redArg___closed__12, &l_LeanExport_M_run___redArg___closed__12_once, _init_l_LeanExport_M_run___redArg___closed__12);
v___x_424_ = lean_apply_3(v_act_421_, v_env_420_, v___x_423_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_fst_429_; lean_object* v___x_431_; 
v_fst_429_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_fst_429_);
lean_dec(v_a_425_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_fst_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_fst_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_424_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_424_);
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
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_LeanExport_M_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_420_ = stack[0].m_obj;
lean_object* v_act_421_ = stack[1].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_LeanExport_M_run___redArg(v_env_420_, v_act_421_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___redArg___boxed(lean_object* v_env_443_, lean_object* v_act_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_LeanExport_M_run___redArg(v_env_443_, v_act_444_);
return v_res_446_;
}
}
lean_object* l_LeanExport_M_run(lean_object* v_00_u03b1_447_, lean_object* v_env_448_, lean_object* v_act_449_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_LeanExport_M_run___redArg(v_env_448_, v_act_449_);
return v___x_451_;
}
}
LEAN_EXPORT void l_LeanExport_M_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_448_ = stack[1].m_obj;
lean_object* v_act_449_ = stack[2].m_obj;
lean_object* v_res_452_;
v_res_452_ = l_LeanExport_M_run(lean_box(0), v_env_448_, v_act_449_);
stack->m_obj
 = v_res_452_;
}
LEAN_EXPORT lean_object* l_LeanExport_M_run___boxed(lean_object* v_00_u03b1_453_, lean_object* v_env_454_, lean_object* v_act_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_LeanExport_M_run(v_00_u03b1_453_, v_env_454_, v_act_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0(lean_object* v_00_u03b2_458_, lean_object* v_m_459_, lean_object* v_a_460_, lean_object* v_b_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_m_459_, v_a_460_, v_b_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1(lean_object* v_00_u03b2_463_, lean_object* v_m_464_, lean_object* v_a_465_, lean_object* v_b_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_m_464_, v_a_465_, v_b_466_);
return v___x_467_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_object* v_00_u03b2_468_, lean_object* v_a_469_, lean_object* v_x_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___redArg(v_a_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_469_ = stack[1].m_obj;
lean_object* v_x_470_ = stack[2].m_obj;
uint8_t v_res_472_;
v_res_472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(lean_box(0), v_a_469_, v_x_470_);
stack->m_num = v_res_472_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0___boxed(lean_object* v_00_u03b2_473_, lean_object* v_a_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__0(v_00_u03b2_473_, v_a_474_, v_x_475_);
lean_dec(v_x_475_);
lean_dec(v_a_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1(lean_object* v_00_u03b2_478_, lean_object* v_data_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1___redArg(v_data_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2(lean_object* v_00_u03b2_481_, lean_object* v_a_482_, lean_object* v_b_483_, lean_object* v_x_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__2___redArg(v_a_482_, v_b_483_, v_x_484_);
return v___x_485_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_object* v_00_u03b2_486_, lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___redArg(v_a_487_, v_x_488_);
return v___x_489_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_487_ = stack[1].m_obj;
lean_object* v_x_488_ = stack[2].m_obj;
uint8_t v_res_490_;
v_res_490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(lean_box(0), v_a_487_, v_x_488_);
stack->m_num = v_res_490_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4___boxed(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__4(v_00_u03b2_491_, v_a_492_, v_x_493_);
lean_dec(v_x_493_);
lean_dec(v_a_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5(lean_object* v_00_u03b2_496_, lean_object* v_data_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5___redArg(v_data_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6(lean_object* v_00_u03b2_499_, lean_object* v_a_500_, lean_object* v_b_501_, lean_object* v_x_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__6___redArg(v_a_500_, v_b_501_, v_x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_504_, lean_object* v_i_505_, lean_object* v_source_506_, lean_object* v_target_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2___redArg(v_i_505_, v_source_506_, v_target_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7(lean_object* v_00_u03b2_509_, lean_object* v_i_510_, lean_object* v_source_511_, lean_object* v_target_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7___redArg(v_i_510_, v_source_511_, v_target_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0_spec__1_spec__2_spec__4___redArg(v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9(lean_object* v_00_u03b2_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1_spec__5_spec__7_spec__9___redArg(v_x_519_, v_x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(lean_object* v_val_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
lean_object* v_toConstantVal_524_; lean_object* v_name_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_toConstantVal_524_ = lean_ctor_get(v_val_522_, 0);
lean_inc_ref(v_toConstantVal_524_);
lean_dec_ref(v_val_522_);
v_name_525_ = lean_ctor_get(v_toConstantVal_524_, 0);
lean_inc(v_name_525_);
lean_dec_ref(v_toConstantVal_524_);
v___x_526_ = l_Lean_NameSet_empty;
v___x_527_ = l_Lean_NameSet_insert(v___x_526_, v_name_525_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v_toConstantVal_529_; lean_object* v_val_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_toConstantVal_529_ = lean_ctor_get(v_val_522_, 0);
lean_inc_ref(v_toConstantVal_529_);
lean_dec_ref(v_val_522_);
v_val_530_ = lean_ctor_get(v_x_523_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v_x_523_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v_x_523_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_val_530_);
lean_dec(v_x_523_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_name_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v_name_534_ = lean_ctor_get(v_toConstantVal_529_, 0);
lean_inc(v_name_534_);
lean_dec_ref(v_toConstantVal_529_);
v___x_535_ = l_Lean_NameSet_insert(v_val_530_, v_name_534_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_535_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(lean_object* v_val_540_, lean_object* v_k_541_, lean_object* v_t_542_){
_start:
{
if (lean_obj_tag(v_t_542_) == 0)
{
lean_object* v_size_543_; lean_object* v_k_544_; lean_object* v_v_545_; lean_object* v_l_546_; lean_object* v_r_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_562_; 
v_size_543_ = lean_ctor_get(v_t_542_, 0);
v_k_544_ = lean_ctor_get(v_t_542_, 1);
v_v_545_ = lean_ctor_get(v_t_542_, 2);
v_l_546_ = lean_ctor_get(v_t_542_, 3);
v_r_547_ = lean_ctor_get(v_t_542_, 4);
v_isSharedCheck_562_ = !lean_is_exclusive(v_t_542_);
if (v_isSharedCheck_562_ == 0)
{
v___x_549_ = v_t_542_;
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_r_547_);
lean_inc(v_l_546_);
lean_inc(v_v_545_);
lean_inc(v_k_544_);
lean_inc(v_size_543_);
lean_dec(v_t_542_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_562_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_541_, v_k_544_);
switch(v___x_551_)
{
case 0:
{
lean_object* v_impl_552_; lean_object* v___x_553_; 
lean_del_object(v___x_549_);
lean_dec(v_size_543_);
v_impl_552_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_540_, v_k_541_, v_l_546_);
v___x_553_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_544_, v_v_545_, v_impl_552_, v_r_547_);
return v___x_553_;
}
case 1:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v_val_556_; lean_object* v___x_558_; 
lean_dec(v_k_544_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_v_545_);
v___x_555_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_540_, v___x_554_);
v_val_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_val_556_);
lean_dec(v___x_555_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v_val_556_);
lean_ctor_set(v___x_549_, 1, v_k_541_);
v___x_558_ = v___x_549_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_size_543_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_k_541_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_val_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_l_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_r_547_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
default: 
{
lean_object* v_impl_560_; lean_object* v___x_561_; 
lean_del_object(v___x_549_);
lean_dec(v_size_543_);
v_impl_560_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_540_, v_k_541_, v_r_547_);
v___x_561_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_544_, v_v_545_, v_l_546_, v_impl_560_);
return v___x_561_;
}
}
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_val_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_563_ = lean_box(0);
v___x_564_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg___lam__0(v_val_540_, v___x_563_);
v_val_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_k_541_);
lean_ctor_set(v___x_567_, 2, v_val_565_);
lean_ctor_set(v___x_567_, 3, v_t_542_);
lean_ctor_set(v___x_567_, 4, v_t_542_);
return v___x_567_;
}
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(lean_object* v_val_568_, lean_object* v_as_x27_569_, lean_object* v_b_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_as_x27_569_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_val_568_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_b_570_);
lean_ctor_set(v___x_573_, 1, v___y_571_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v_head_575_; lean_object* v_tail_576_; lean_object* v___x_577_; 
v_head_575_ = lean_ctor_get(v_as_x27_569_, 0);
v_tail_576_ = lean_ctor_get(v_as_x27_569_, 1);
lean_inc(v_head_575_);
lean_inc_ref(v_val_568_);
v___x_577_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_568_, v_head_575_, v_b_570_);
v_as_x27_569_ = v_tail_576_;
v_b_570_ = v___x_577_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_568_ = stack[0].m_obj;
lean_object* v_as_x27_569_ = stack[1].m_obj;
lean_object* v_b_570_ = stack[2].m_obj;
lean_object* v___y_571_ = stack[3].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_568_, v_as_x27_569_, v_b_570_, v___y_571_);
stack->m_obj
 = v_res_579_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg___boxed(lean_object* v_val_580_, lean_object* v_as_x27_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_580_, v_as_x27_581_, v_b_582_, v___y_583_);
lean_dec(v_as_x27_581_);
return v_res_585_;
}
}
lean_object* l_LeanExport_initState___lam__0(lean_object* v_x_586_, lean_object* v_y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_a_593_; lean_object* v_snd_594_; 
if (lean_obj_tag(v_y_587_) == 7)
{
lean_object* v_val_600_; lean_object* v_all_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; 
v_val_600_ = lean_ctor_get(v_y_587_, 0);
lean_inc_ref(v_val_600_);
lean_dec_ref_known(v_y_587_, 1);
v_all_601_ = lean_ctor_get(v_val_600_, 1);
lean_inc(v_all_601_);
v___x_602_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_600_, v_all_601_, v___y_588_, v___y_590_);
lean_dec(v_all_601_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
v_fst_604_ = lean_ctor_get(v_a_603_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v_a_603_, 1);
lean_inc(v_snd_605_);
lean_dec(v_a_603_);
v_a_593_ = v_fst_604_;
v_snd_594_ = v_snd_605_;
goto v___jp_592_;
}
else
{
lean_dec_ref(v_y_587_);
v_a_593_ = v___y_588_;
v_snd_594_ = v___y_590_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_a_593_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v_snd_594_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
}
LEAN_EXPORT void l_LeanExport_initState___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_586_ = stack[0].m_obj;
lean_object* v_y_587_ = stack[1].m_obj;
lean_object* v___y_588_ = stack[2].m_obj;
lean_object* v___y_589_ = stack[3].m_obj;
lean_object* v___y_590_ = stack[4].m_obj;
lean_object* v_res_606_;
v_res_606_ = l_LeanExport_initState___lam__0(v_x_586_, v_y_587_, v___y_588_, v___y_589_, v___y_590_);
stack->m_obj
 = v_res_606_;
}
LEAN_EXPORT lean_object* l_LeanExport_initState___lam__0___boxed(lean_object* v_x_607_, lean_object* v_y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_LeanExport_initState___lam__0(v_x_607_, v_y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v_x_607_);
return v_res_613_;
}
}
uint8_t l_List_any___at___00LeanExport_initState_spec__2(lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
else
{
lean_object* v_head_617_; lean_object* v_tail_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_head_617_ = lean_ctor_get(v_x_615_, 0);
v_tail_618_ = lean_ctor_get(v_x_615_, 1);
v___x_619_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__2___closed__0));
v___x_620_ = lean_string_dec_eq(v_head_617_, v___x_619_);
if (v___x_620_ == 0)
{
v_x_615_ = v_tail_618_;
goto _start;
}
else
{
return v___x_620_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00LeanExport_initState_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_615_ = stack[0].m_obj;
uint8_t v_res_622_;
v_res_622_ = l_List_any___at___00LeanExport_initState_spec__2(v_x_615_);
stack->m_num = v_res_622_;
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__2___boxed(lean_object* v_x_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_List_any___at___00LeanExport_initState_spec__2(v_x_623_);
lean_dec(v_x_623_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
uint8_t l_List_any___at___00LeanExport_initState_spec__0(lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
uint8_t v___x_628_; 
v___x_628_ = 0;
return v___x_628_;
}
else
{
lean_object* v_head_629_; lean_object* v_tail_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_head_629_ = lean_ctor_get(v_x_627_, 0);
v_tail_630_ = lean_ctor_get(v_x_627_, 1);
v___x_631_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__0___closed__0));
v___x_632_ = lean_string_dec_eq(v_head_629_, v___x_631_);
if (v___x_632_ == 0)
{
v_x_627_ = v_tail_630_;
goto _start;
}
else
{
return v___x_632_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00LeanExport_initState_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_627_ = stack[0].m_obj;
uint8_t v_res_634_;
v_res_634_ = l_List_any___at___00LeanExport_initState_spec__0(v_x_627_);
stack->m_num = v_res_634_;
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__0___boxed(lean_object* v_x_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_List_any___at___00LeanExport_initState_spec__0(v_x_635_);
lean_dec(v_x_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(lean_object* v_f_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_f_638_);
v___x_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_645_, 0, v_x_639_);
lean_ctor_set(v___x_645_, 1, v___y_641_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v___y_643_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_key_649_; lean_object* v_value_650_; lean_object* v_tail_651_; lean_object* v___x_652_; 
v_key_649_ = lean_ctor_get(v_x_640_, 0);
lean_inc(v_key_649_);
v_value_650_ = lean_ctor_get(v_x_640_, 1);
lean_inc(v_value_650_);
v_tail_651_ = lean_ctor_get(v_x_640_, 2);
lean_inc(v_tail_651_);
lean_dec_ref_known(v_x_640_, 3);
lean_inc_ref(v_f_638_);
lean_inc_ref(v___y_642_);
v___x_652_ = lean_apply_6(v_f_638_, v_key_649_, v_value_650_, v___y_641_, v___y_642_, v___y_643_, lean_box(0));
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_fst_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
v_fst_654_ = lean_ctor_get(v_a_653_, 0);
if (lean_obj_tag(v_fst_654_) == 0)
{
lean_dec(v_a_653_);
lean_dec(v_tail_651_);
lean_dec_ref(v_f_638_);
return v___x_652_;
}
else
{
lean_object* v_a_655_; lean_object* v_snd_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; 
lean_dec_ref_known(v___x_652_, 1);
v_a_655_ = lean_ctor_get(v_fst_654_, 0);
lean_inc(v_a_655_);
v_snd_656_ = lean_ctor_get(v_a_653_, 1);
lean_inc(v_snd_656_);
lean_dec(v_a_653_);
v_fst_657_ = lean_ctor_get(v_a_655_, 0);
lean_inc(v_fst_657_);
v_snd_658_ = lean_ctor_get(v_a_655_, 1);
lean_inc(v_snd_658_);
lean_dec(v_a_655_);
v_x_639_ = v_fst_657_;
v_x_640_ = v_tail_651_;
v___y_641_ = v_snd_658_;
v___y_643_ = v_snd_656_;
goto _start;
}
}
else
{
lean_dec(v_tail_651_);
lean_dec_ref(v_f_638_);
return v___x_652_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_638_ = stack[0].m_obj;
lean_object* v_x_639_ = stack[1].m_obj;
lean_object* v_x_640_ = stack[2].m_obj;
lean_object* v___y_641_ = stack[3].m_obj;
lean_object* v___y_642_ = stack[4].m_obj;
lean_object* v___y_643_ = stack[5].m_obj;
lean_object* v_res_660_;
v_res_660_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_638_, v_x_639_, v_x_640_, v___y_641_, v___y_642_, v___y_643_);
stack->m_obj
 = v_res_660_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg___boxed(lean_object* v_f_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_661_, v_x_662_, v_x_663_, v___y_664_, v___y_665_, v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_668_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(lean_object* v_f_669_, lean_object* v_as_670_, size_t v_i_671_, size_t v_stop_672_, lean_object* v_b_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
uint8_t v___x_678_; 
v___x_678_ = lean_usize_dec_eq(v_i_671_, v_stop_672_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_array_uget_borrowed(v_as_670_, v_i_671_);
v___x_680_ = lean_box(0);
lean_inc(v___x_679_);
lean_inc_ref(v_f_669_);
v___x_681_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_669_, v___x_680_, v___x_679_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v_fst_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
v_fst_683_ = lean_ctor_get(v_a_682_, 0);
if (lean_obj_tag(v_fst_683_) == 0)
{
lean_dec_ref(v_f_669_);
return v___x_681_;
}
else
{
lean_object* v_a_684_; lean_object* v_snd_685_; lean_object* v_fst_686_; lean_object* v_snd_687_; size_t v___x_688_; size_t v___x_689_; 
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v_a_684_ = lean_ctor_get(v_fst_683_, 0);
lean_inc(v_a_684_);
v_snd_685_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_685_);
lean_dec(v_a_682_);
v_fst_686_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_fst_686_);
v_snd_687_ = lean_ctor_get(v_a_684_, 1);
lean_inc(v_snd_687_);
lean_dec(v_a_684_);
v___x_688_ = ((size_t)1ULL);
v___x_689_ = lean_usize_add(v_i_671_, v___x_688_);
v_i_671_ = v___x_689_;
v_b_673_ = v_fst_686_;
v___y_674_ = v_snd_687_;
v___y_676_ = v_snd_685_;
goto _start;
}
}
else
{
lean_dec_ref(v_f_669_);
return v___x_681_;
}
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v_f_669_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v_b_673_);
lean_ctor_set(v___x_691_, 1, v___y_674_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___y_676_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_669_ = stack[0].m_obj;
lean_object* v_as_670_ = stack[1].m_obj;
size_t v_i_671_ = stack[2].m_num;
size_t v_stop_672_ = stack[3].m_num;
lean_object* v_b_673_ = stack[4].m_obj;
lean_object* v___y_674_ = stack[5].m_obj;
lean_object* v___y_675_ = stack[6].m_obj;
lean_object* v___y_676_ = stack[7].m_obj;
lean_object* v_res_695_;
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_669_, v_as_670_, v_i_671_, v_stop_672_, v_b_673_, v___y_674_, v___y_675_, v___y_676_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg___boxed(lean_object* v_f_696_, lean_object* v_as_697_, lean_object* v_i_698_, lean_object* v_stop_699_, lean_object* v_b_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
size_t v_i_boxed_705_; size_t v_stop_boxed_706_; lean_object* v_res_707_; 
v_i_boxed_705_ = lean_unbox_usize(v_i_698_);
lean_dec(v_i_698_);
v_stop_boxed_706_ = lean_unbox_usize(v_stop_699_);
lean_dec(v_stop_699_);
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_696_, v_as_697_, v_i_boxed_705_, v_stop_boxed_706_, v_b_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_as_697_);
return v_res_707_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(lean_object* v_f_708_, lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
lean_inc_ref(v___y_713_);
v___x_716_ = lean_apply_6(v_f_708_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, lean_box(0));
return v___x_716_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_708_ = stack[0].m_obj;
lean_object* v_x_709_ = stack[1].m_obj;
lean_object* v___y_710_ = stack[2].m_obj;
lean_object* v___y_711_ = stack[3].m_obj;
lean_object* v___y_712_ = stack[4].m_obj;
lean_object* v___y_713_ = stack[5].m_obj;
lean_object* v___y_714_ = stack[6].m_obj;
lean_object* v_res_717_;
v_res_717_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_708_, v_x_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
stack->m_obj
 = v_res_717_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed(lean_object* v_f_718_, lean_object* v_x_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0(v_f_718_, v_x_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec_ref(v___y_723_);
return v_res_726_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(lean_object* v_f_727_, lean_object* v_keys_728_, lean_object* v_vals_729_, lean_object* v_i_730_, lean_object* v_acc_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = lean_array_get_size(v_keys_728_);
v___x_737_ = lean_nat_dec_lt(v_i_730_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_i_730_);
lean_dec_ref(v_f_727_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_acc_731_);
lean_ctor_set(v___x_738_, 1, v___y_732_);
v___x_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___y_734_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_k_742_; lean_object* v_v_743_; lean_object* v___x_744_; 
v_k_742_ = lean_array_fget_borrowed(v_keys_728_, v_i_730_);
v_v_743_ = lean_array_fget_borrowed(v_vals_729_, v_i_730_);
lean_inc_ref(v_f_727_);
lean_inc_ref(v___y_733_);
lean_inc(v_v_743_);
lean_inc(v_k_742_);
v___x_744_ = lean_apply_7(v_f_727_, v_acc_731_, v_k_742_, v_v_743_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_fst_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
v_fst_746_ = lean_ctor_get(v_a_745_, 0);
if (lean_obj_tag(v_fst_746_) == 0)
{
lean_dec(v_a_745_);
lean_dec(v_i_730_);
lean_dec_ref(v_f_727_);
return v___x_744_;
}
else
{
lean_object* v_a_747_; lean_object* v_snd_748_; lean_object* v_fst_749_; lean_object* v_snd_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref_known(v___x_744_, 1);
v_a_747_ = lean_ctor_get(v_fst_746_, 0);
lean_inc(v_a_747_);
v_snd_748_ = lean_ctor_get(v_a_745_, 1);
lean_inc(v_snd_748_);
lean_dec(v_a_745_);
v_fst_749_ = lean_ctor_get(v_a_747_, 0);
lean_inc(v_fst_749_);
v_snd_750_ = lean_ctor_get(v_a_747_, 1);
lean_inc(v_snd_750_);
lean_dec(v_a_747_);
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = lean_nat_add(v_i_730_, v___x_751_);
lean_dec(v_i_730_);
v_i_730_ = v___x_752_;
v_acc_731_ = v_fst_749_;
v___y_732_ = v_snd_750_;
v___y_734_ = v_snd_748_;
goto _start;
}
}
else
{
lean_dec(v_i_730_);
lean_dec_ref(v_f_727_);
return v___x_744_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_727_ = stack[0].m_obj;
lean_object* v_keys_728_ = stack[1].m_obj;
lean_object* v_vals_729_ = stack[2].m_obj;
lean_object* v_i_730_ = stack[3].m_obj;
lean_object* v_acc_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v_res_754_;
v_res_754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_727_, v_keys_728_, v_vals_729_, v_i_730_, v_acc_731_, v___y_732_, v___y_733_, v___y_734_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg___boxed(lean_object* v_f_755_, lean_object* v_keys_756_, lean_object* v_vals_757_, lean_object* v_i_758_, lean_object* v_acc_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_755_, v_keys_756_, v_vals_757_, v_i_758_, v_acc_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec_ref(v_vals_757_);
lean_dec_ref(v_keys_756_);
return v_res_764_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_f_765_, lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v_snd_777_; lean_object* v___y_782_; uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
v___x_790_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
switch(lean_obj_tag(v___x_790_))
{
case 0:
{
lean_object* v_key_791_; lean_object* v_val_792_; lean_object* v___x_793_; 
v_key_791_ = lean_ctor_get(v___x_790_, 0);
v_val_792_ = lean_ctor_get(v___x_790_, 1);
lean_inc_ref(v_f_765_);
lean_inc_ref(v___y_771_);
lean_inc(v_val_792_);
lean_inc(v_key_791_);
v___x_793_ = lean_apply_7(v_f_765_, v_b_769_, v_key_791_, v_val_792_, v___y_770_, v___y_771_, v___y_772_, lean_box(0));
v___y_782_ = v___x_793_;
goto v___jp_781_;
}
case 1:
{
lean_object* v_node_794_; lean_object* v___x_795_; 
v_node_794_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_node_794_);
lean_inc_ref(v_f_765_);
v___x_795_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_765_, v_node_794_, v_b_769_, v___y_770_, v___y_771_, v___y_772_);
v___y_782_ = v___x_795_;
goto v___jp_781_;
}
default: 
{
v_fst_775_ = v_b_769_;
v_snd_776_ = v___y_770_;
v_snd_777_ = v___y_772_;
goto v___jp_774_;
}
}
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_dec_ref(v_f_765_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_b_769_);
lean_ctor_set(v___x_796_, 1, v___y_770_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___y_772_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
v___jp_774_:
{
size_t v___x_778_; size_t v___x_779_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_767_, v___x_778_);
v_i_767_ = v___x_779_;
v_b_769_ = v_fst_775_;
v___y_770_ = v_snd_776_;
v___y_772_ = v_snd_777_;
goto _start;
}
v___jp_781_:
{
if (lean_obj_tag(v___y_782_) == 0)
{
lean_object* v_a_783_; lean_object* v_fst_784_; 
v_a_783_ = lean_ctor_get(v___y_782_, 0);
v_fst_784_ = lean_ctor_get(v_a_783_, 0);
if (lean_obj_tag(v_fst_784_) == 0)
{
lean_dec_ref(v_f_765_);
return v___y_782_;
}
else
{
lean_object* v_a_785_; lean_object* v_snd_786_; lean_object* v_fst_787_; lean_object* v_snd_788_; 
lean_inc(v_a_783_);
lean_dec_ref_known(v___y_782_, 1);
v_a_785_ = lean_ctor_get(v_fst_784_, 0);
lean_inc(v_a_785_);
v_snd_786_ = lean_ctor_get(v_a_783_, 1);
lean_inc(v_snd_786_);
lean_dec(v_a_783_);
v_fst_787_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_fst_787_);
v_snd_788_ = lean_ctor_get(v_a_785_, 1);
lean_inc(v_snd_788_);
lean_dec(v_a_785_);
v_fst_775_ = v_fst_787_;
v_snd_776_ = v_snd_788_;
v_snd_777_ = v_snd_786_;
goto v___jp_774_;
}
}
else
{
lean_dec_ref(v_f_765_);
return v___y_782_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_765_ = stack[0].m_obj;
lean_object* v_as_766_ = stack[1].m_obj;
size_t v_i_767_ = stack[2].m_num;
size_t v_stop_768_ = stack[3].m_num;
lean_object* v_b_769_ = stack[4].m_obj;
lean_object* v___y_770_ = stack[5].m_obj;
lean_object* v___y_771_ = stack[6].m_obj;
lean_object* v___y_772_ = stack[7].m_obj;
lean_object* v_res_800_;
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_765_, v_as_766_, v_i_767_, v_stop_768_, v_b_769_, v___y_770_, v___y_771_, v___y_772_);
stack->m_obj
 = v_res_800_;
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_f_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v_es_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_824_; 
v_es_808_ = lean_ctor_get(v_x_802_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_824_ == 0)
{
v___x_810_ = v_x_802_;
v_isShared_811_ = v_isSharedCheck_824_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_es_808_);
lean_dec(v_x_802_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_824_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_array_get_size(v_es_808_);
v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec_ref(v_es_808_);
lean_dec_ref(v_f_801_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_x_803_);
lean_ctor_set(v___x_815_, 1, v___y_804_);
if (v_isShared_811_ == 0)
{
lean_ctor_set_tag(v___x_810_, 1);
lean_ctor_set(v___x_810_, 0, v___x_815_);
v___x_817_ = v___x_810_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_820_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___y_806_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
else
{
size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_810_);
v___x_821_ = ((size_t)0ULL);
v___x_822_ = lean_usize_of_nat(v___x_813_);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_801_, v_es_808_, v___x_821_, v___x_822_, v_x_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec_ref(v_es_808_);
return v___x_823_;
}
}
}
else
{
lean_object* v_ks_825_; lean_object* v_vs_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_ks_825_ = lean_ctor_get(v_x_802_, 0);
lean_inc_ref(v_ks_825_);
v_vs_826_ = lean_ctor_get(v_x_802_, 1);
lean_inc_ref(v_vs_826_);
lean_dec_ref_known(v_x_802_, 2);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_801_, v_ks_825_, v_vs_826_, v___x_827_, v_x_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec_ref(v_vs_826_);
lean_dec_ref(v_ks_825_);
return v___x_828_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_801_ = stack[0].m_obj;
lean_object* v_x_802_ = stack[1].m_obj;
lean_object* v_x_803_ = stack[2].m_obj;
lean_object* v___y_804_ = stack[3].m_obj;
lean_object* v___y_805_ = stack[4].m_obj;
lean_object* v___y_806_ = stack[5].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_801_, v_x_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_f_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_830_, v_x_831_, v_x_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_f_838_, lean_object* v_as_839_, lean_object* v_i_840_, lean_object* v_stop_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
size_t v_i_boxed_847_; size_t v_stop_boxed_848_; lean_object* v_res_849_; 
v_i_boxed_847_ = lean_unbox_usize(v_i_840_);
lean_dec(v_i_840_);
v_stop_boxed_848_ = lean_unbox_usize(v_stop_841_);
lean_dec(v_stop_841_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_838_, v_as_839_, v_i_boxed_847_, v_stop_boxed_848_, v_b_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_as_839_);
return v_res_849_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(lean_object* v_map_850_, lean_object* v_f_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___f_856_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_856_, 0, v_f_851_);
v___x_857_ = lean_box(0);
v___x_858_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v___f_856_, v_map_850_, v___x_857_, v___y_852_, v___y_853_, v___y_854_);
return v___x_858_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_850_ = stack[0].m_obj;
lean_object* v_f_851_ = stack[1].m_obj;
lean_object* v___y_852_ = stack[2].m_obj;
lean_object* v___y_853_ = stack[3].m_obj;
lean_object* v___y_854_ = stack[4].m_obj;
lean_object* v_res_859_;
v_res_859_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_850_, v_f_851_, v___y_852_, v___y_853_, v___y_854_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg___boxed(lean_object* v_map_860_, lean_object* v_f_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_860_, v_f_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec_ref(v___y_863_);
return v_res_866_;
}
}
lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(lean_object* v_s_867_, lean_object* v_f_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_map_u2081_873_; lean_object* v_map_u2082_874_; lean_object* v_buckets_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_map_u2081_873_ = lean_ctor_get(v_s_867_, 0);
lean_inc_ref(v_map_u2081_873_);
v_map_u2082_874_ = lean_ctor_get(v_s_867_, 1);
lean_inc_ref(v_map_u2082_874_);
lean_dec_ref(v_s_867_);
v_buckets_875_ = lean_ctor_get(v_map_u2081_873_, 1);
lean_inc_ref(v_buckets_875_);
lean_dec_ref(v_map_u2081_873_);
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_array_get_size(v_buckets_875_);
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; 
lean_dec_ref(v_buckets_875_);
v___x_879_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_874_, v_f_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_880_ = lean_box(0);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_877_);
lean_inc_ref(v_f_868_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_868_, v_buckets_875_, v___x_881_, v___x_882_, v___x_880_, v___y_869_, v___y_870_, v___y_871_);
lean_dec_ref(v_buckets_875_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_fst_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_fst_885_ = lean_ctor_get(v_a_884_, 0);
if (lean_obj_tag(v_fst_885_) == 0)
{
lean_dec_ref(v_map_u2082_874_);
lean_dec_ref(v_f_868_);
return v___x_883_;
}
else
{
lean_object* v_a_886_; lean_object* v_snd_887_; lean_object* v_snd_888_; lean_object* v___x_889_; 
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v_a_886_ = lean_ctor_get(v_fst_885_, 0);
lean_inc(v_a_886_);
v_snd_887_ = lean_ctor_get(v_a_884_, 1);
lean_inc(v_snd_887_);
lean_dec(v_a_884_);
v_snd_888_ = lean_ctor_get(v_a_886_, 1);
lean_inc(v_snd_888_);
lean_dec(v_a_886_);
v___x_889_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_u2082_874_, v_f_868_, v_snd_888_, v___y_870_, v_snd_887_);
return v___x_889_;
}
}
else
{
lean_dec_ref(v_map_u2082_874_);
lean_dec_ref(v_f_868_);
return v___x_883_;
}
}
}
}
LEAN_EXPORT void l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_867_ = stack[0].m_obj;
lean_object* v_f_868_ = stack[1].m_obj;
lean_object* v___y_869_ = stack[2].m_obj;
lean_object* v___y_870_ = stack[3].m_obj;
lean_object* v___y_871_ = stack[4].m_obj;
lean_object* v_res_890_;
v_res_890_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_867_, v_f_868_, v___y_869_, v___y_870_, v___y_871_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg___boxed(lean_object* v_s_891_, lean_object* v_f_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_891_, v_f_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_897_;
}
}
uint8_t l_List_any___at___00LeanExport_initState_spec__1(lean_object* v_x_899_){
_start:
{
if (lean_obj_tag(v_x_899_) == 0)
{
uint8_t v___x_900_; 
v___x_900_ = 0;
return v___x_900_;
}
else
{
lean_object* v_head_901_; lean_object* v_tail_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_head_901_ = lean_ctor_get(v_x_899_, 0);
v_tail_902_ = lean_ctor_get(v_x_899_, 1);
v___x_903_ = ((lean_object*)(l_List_any___at___00LeanExport_initState_spec__1___closed__0));
v___x_904_ = lean_string_dec_eq(v_head_901_, v___x_903_);
if (v___x_904_ == 0)
{
v_x_899_ = v_tail_902_;
goto _start;
}
else
{
return v___x_904_;
}
}
}
}
LEAN_EXPORT void l_List_any___at___00LeanExport_initState_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_899_ = stack[0].m_obj;
uint8_t v_res_906_;
v_res_906_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_899_);
stack->m_num = v_res_906_;
}
LEAN_EXPORT lean_object* l_List_any___at___00LeanExport_initState_spec__1___boxed(lean_object* v_x_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_List_any___at___00LeanExport_initState_spec__1(v_x_907_);
lean_dec(v_x_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
lean_object* l_LeanExport_initState(lean_object* v_env_911_, lean_object* v_cliOptions_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___f_938_; lean_object* v_recursorMap_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___f_938_ = ((lean_object*)(l_LeanExport_initState___closed__0));
v_recursorMap_939_ = lean_box(1);
v___x_940_ = l_Lean_Environment_constants(v_env_911_);
v___x_941_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v___x_940_, v___f_938_, v_recursorMap_939_, v_a_913_, v_a_914_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_fst_943_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v_fst_943_ = lean_ctor_get(v_a_942_, 0);
if (lean_obj_tag(v_fst_943_) == 0)
{
lean_object* v_snd_944_; lean_object* v_a_945_; 
lean_inc_ref(v_fst_943_);
v_snd_944_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_snd_944_);
lean_dec(v_a_942_);
v_a_945_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v_fst_943_, 1);
v_fst_917_ = v_a_945_;
v_snd_918_ = v_snd_944_;
goto v___jp_916_;
}
else
{
lean_object* v_a_946_; lean_object* v_snd_947_; lean_object* v_snd_948_; 
v_a_946_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_a_946_);
v_snd_947_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_snd_947_);
lean_dec(v_a_942_);
v_snd_948_ = lean_ctor_get(v_a_946_, 1);
lean_inc(v_snd_948_);
lean_dec(v_a_946_);
v_fst_917_ = v_snd_948_;
v_snd_918_ = v_snd_947_;
goto v___jp_916_;
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
v_a_949_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_941_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_941_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
v___jp_916_:
{
lean_object* v_visitedNames_919_; lean_object* v_visitedLevels_920_; lean_object* v_visitedExprs_921_; lean_object* v_visitedConstants_922_; lean_object* v_noMDataExprs_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_936_; 
v_visitedNames_919_ = lean_ctor_get(v_snd_918_, 0);
v_visitedLevels_920_ = lean_ctor_get(v_snd_918_, 1);
v_visitedExprs_921_ = lean_ctor_get(v_snd_918_, 2);
v_visitedConstants_922_ = lean_ctor_get(v_snd_918_, 3);
v_noMDataExprs_923_ = lean_ctor_get(v_snd_918_, 4);
v_isSharedCheck_936_ = !lean_is_exclusive(v_snd_918_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_snd_918_, 5);
lean_dec(v_unused_937_);
v___x_925_ = v_snd_918_;
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_noMDataExprs_923_);
lean_inc(v_visitedConstants_922_);
lean_inc(v_visitedExprs_921_);
lean_inc(v_visitedLevels_920_);
lean_inc(v_visitedNames_919_);
lean_dec(v_snd_918_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_936_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; uint8_t v___x_928_; uint8_t v___x_929_; uint8_t v___x_930_; lean_object* v___x_932_; 
v___x_927_ = lean_box(0);
v___x_928_ = l_List_any___at___00LeanExport_initState_spec__0(v_cliOptions_912_);
v___x_929_ = l_List_any___at___00LeanExport_initState_spec__1(v_cliOptions_912_);
v___x_930_ = l_List_any___at___00LeanExport_initState_spec__2(v_cliOptions_912_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 5, v_fst_917_);
v___x_932_ = v___x_925_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_visitedNames_919_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_visitedLevels_920_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_visitedExprs_921_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_visitedConstants_922_);
lean_ctor_set(v_reuseFailAlloc_935_, 4, v_noMDataExprs_923_);
lean_ctor_set(v_reuseFailAlloc_935_, 5, v_fst_917_);
v___x_932_ = v_reuseFailAlloc_935_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*6, v___x_928_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*6 + 1, v___x_929_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*6 + 2, v___x_930_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_927_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT void l_LeanExport_initState_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_911_ = stack[0].m_obj;
lean_object* v_cliOptions_912_ = stack[1].m_obj;
lean_object* v_a_913_ = stack[2].m_obj;
lean_object* v_a_914_ = stack[3].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_LeanExport_initState(v_env_911_, v_cliOptions_912_, v_a_913_, v_a_914_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l_LeanExport_initState___boxed(lean_object* v_env_958_, lean_object* v_cliOptions_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_LeanExport_initState(v_env_958_, v_cliOptions_959_, v_a_960_, v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_cliOptions_959_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3(lean_object* v_val_964_, lean_object* v_k_965_, lean_object* v_t_966_, lean_object* v_hl_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00LeanExport_initState_spec__3___redArg(v_val_964_, v_k_965_, v_t_966_);
return v___x_968_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(lean_object* v_val_969_, lean_object* v_as_970_, lean_object* v_as_x27_971_, lean_object* v_b_972_, lean_object* v_a_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___redArg(v_val_969_, v_as_x27_971_, v_b_972_, v___y_975_);
return v___x_977_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_969_ = stack[0].m_obj;
lean_object* v_as_970_ = stack[1].m_obj;
lean_object* v_as_x27_971_ = stack[2].m_obj;
lean_object* v_b_972_ = stack[3].m_obj;
lean_object* v___y_974_ = stack[5].m_obj;
lean_object* v___y_975_ = stack[6].m_obj;
lean_object* v_res_978_;
v_res_978_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_969_, v_as_970_, v_as_x27_971_, v_b_972_, lean_box(0), v___y_974_, v___y_975_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4___boxed(lean_object* v_val_979_, lean_object* v_as_980_, lean_object* v_as_x27_981_, lean_object* v_b_982_, lean_object* v_a_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_List_forIn_x27_loop___at___00LeanExport_initState_spec__4(v_val_979_, v_as_980_, v_as_x27_981_, v_b_982_, v_a_983_, v___y_984_, v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v_as_x27_981_);
lean_dec(v_as_980_);
return v_res_987_;
}
}
lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_object* v_00_u03b2_988_, lean_object* v_s_989_, lean_object* v_f_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___redArg(v_s_989_, v_f_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT void l_Lean_SMap_forM___at___00LeanExport_initState_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_989_ = stack[1].m_obj;
lean_object* v_f_990_ = stack[2].m_obj;
lean_object* v___y_991_ = stack[3].m_obj;
lean_object* v___y_992_ = stack[4].m_obj;
lean_object* v___y_993_ = stack[5].m_obj;
lean_object* v_res_996_;
v_res_996_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(lean_box(0), v_s_989_, v_f_990_, v___y_991_, v___y_992_, v___y_993_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___00LeanExport_initState_spec__5___boxed(lean_object* v_00_u03b2_997_, lean_object* v_s_998_, lean_object* v_f_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_SMap_forM___at___00LeanExport_initState_spec__5(v_00_u03b2_997_, v_s_998_, v_f_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1004_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_object* v_00_u03b2_1005_, lean_object* v_f_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___redArg(v_f_1006_, v_x_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1006_ = stack[1].m_obj;
lean_object* v_x_1007_ = stack[2].m_obj;
lean_object* v_x_1008_ = stack[3].m_obj;
lean_object* v___y_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v___y_1011_ = stack[6].m_obj;
lean_object* v_res_1014_;
v_res_1014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(lean_box(0), v_f_1006_, v_x_1007_, v_x_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
stack->m_obj
 = v_res_1014_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5___boxed(lean_object* v_00_u03b2_1015_, lean_object* v_f_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__5(v_00_u03b2_1015_, v_f_1016_, v_x_1017_, v_x_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_object* v_00_u03b2_1024_, lean_object* v_map_1025_, lean_object* v_f_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___redArg(v_map_1025_, v_f_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_1025_ = stack[1].m_obj;
lean_object* v_f_1026_ = stack[2].m_obj;
lean_object* v___y_1027_ = stack[3].m_obj;
lean_object* v___y_1028_ = stack[4].m_obj;
lean_object* v___y_1029_ = stack[5].m_obj;
lean_object* v_res_1032_;
v_res_1032_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(lean_box(0), v_map_1025_, v_f_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
stack->m_obj
 = v_res_1032_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_map_1034_, lean_object* v_f_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6(v_00_u03b2_1033_, v_map_1034_, v_f_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_object* v_00_u03b2_1041_, lean_object* v_f_1042_, lean_object* v_as_1043_, size_t v_i_1044_, size_t v_stop_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___redArg(v_f_1042_, v_as_1043_, v_i_1044_, v_stop_1045_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1042_ = stack[1].m_obj;
lean_object* v_as_1043_ = stack[2].m_obj;
size_t v_i_1044_ = stack[3].m_num;
size_t v_stop_1045_ = stack[4].m_num;
lean_object* v_b_1046_ = stack[5].m_obj;
lean_object* v___y_1047_ = stack[6].m_obj;
lean_object* v___y_1048_ = stack[7].m_obj;
lean_object* v___y_1049_ = stack[8].m_obj;
lean_object* v_res_1052_;
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(lean_box(0), v_f_1042_, v_as_1043_, v_i_1044_, v_stop_1045_, v_b_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
stack->m_obj
 = v_res_1052_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1053_, lean_object* v_f_1054_, lean_object* v_as_1055_, lean_object* v_i_1056_, lean_object* v_stop_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
size_t v_i_boxed_1063_; size_t v_stop_boxed_1064_; lean_object* v_res_1065_; 
v_i_boxed_1063_ = lean_unbox_usize(v_i_1056_);
lean_dec(v_i_1056_);
v_stop_boxed_1064_ = lean_unbox_usize(v_stop_1057_);
lean_dec(v_stop_1057_);
v_res_1065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__7(v_00_u03b2_1053_, v_f_1054_, v_as_1055_, v_i_boxed_1063_, v_stop_boxed_1064_, v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec_ref(v_as_1055_);
return v_res_1065_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(lean_object* v_map_1066_, lean_object* v_f_1067_, lean_object* v_init_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1067_, v_map_1066_, v_init_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_1066_ = stack[0].m_obj;
lean_object* v_f_1067_ = stack[1].m_obj;
lean_object* v_init_1068_ = stack[2].m_obj;
lean_object* v___y_1069_ = stack[3].m_obj;
lean_object* v___y_1070_ = stack[4].m_obj;
lean_object* v___y_1071_ = stack[5].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1066_, v_f_1067_, v_init_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_map_1075_, lean_object* v_f_1076_, lean_object* v_init_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___redArg(v_map_1075_, v_f_1076_, v_init_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1082_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_object* v_00_u03c3_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_map_1085_, lean_object* v_f_1086_, lean_object* v_init_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1086_, v_map_1085_, v_init_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_map_1085_ = stack[2].m_obj;
lean_object* v_f_1086_ = stack[3].m_obj;
lean_object* v_init_1087_ = stack[4].m_obj;
lean_object* v___y_1088_ = stack[5].m_obj;
lean_object* v___y_1089_ = stack[6].m_obj;
lean_object* v___y_1090_ = stack[7].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(lean_box(0), lean_box(0), v_map_1085_, v_f_1086_, v_init_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03c3_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_map_1096_, lean_object* v_f_1097_, lean_object* v_init_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7(v_00_u03c3_1094_, v_00_u03b2_1095_, v_map_1096_, v_f_1097_, v_init_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1103_;
}
}
lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03c3_1104_, lean_object* v_00_u03b1_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_f_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___redArg(v_f_1107_, v_x_1108_, v_x_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1107_ = stack[3].m_obj;
lean_object* v_x_1108_ = stack[4].m_obj;
lean_object* v_x_1109_ = stack[5].m_obj;
lean_object* v___y_1110_ = stack[6].m_obj;
lean_object* v___y_1111_ = stack[7].m_obj;
lean_object* v___y_1112_ = stack[8].m_obj;
lean_object* v_res_1115_;
v_res_1115_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(lean_box(0), lean_box(0), lean_box(0), v_f_1107_, v_x_1108_, v_x_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1115_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03c3_1116_, lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_f_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8(v_00_u03c3_1116_, v_00_u03b1_1117_, v_00_u03b2_1118_, v_f_1119_, v_x_1120_, v_x_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1126_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_1127_, lean_object* v_00_u03b2_1128_, lean_object* v_00_u03c3_1129_, lean_object* v_f_1130_, lean_object* v_as_1131_, size_t v_i_1132_, size_t v_stop_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___redArg(v_f_1130_, v_as_1131_, v_i_1132_, v_stop_1133_, v_b_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1130_ = stack[3].m_obj;
lean_object* v_as_1131_ = stack[4].m_obj;
size_t v_i_1132_ = stack[5].m_num;
size_t v_stop_1133_ = stack[6].m_num;
lean_object* v_b_1134_ = stack[7].m_obj;
lean_object* v___y_1135_ = stack[8].m_obj;
lean_object* v___y_1136_ = stack[9].m_obj;
lean_object* v___y_1137_ = stack[10].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(lean_box(0), lean_box(0), lean_box(0), v_f_1130_, v_as_1131_, v_i_1132_, v_stop_1133_, v_b_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1140_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_00_u03c3_1143_, lean_object* v_f_1144_, lean_object* v_as_1145_, lean_object* v_i_1146_, lean_object* v_stop_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
size_t v_i_boxed_1153_; size_t v_stop_boxed_1154_; lean_object* v_res_1155_; 
v_i_boxed_1153_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_stop_boxed_1154_ = lean_unbox_usize(v_stop_1147_);
lean_dec(v_stop_1147_);
v_res_1155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_1141_, v_00_u03b2_1142_, v_00_u03c3_1143_, v_f_1144_, v_as_1145_, v_i_boxed_1153_, v_stop_boxed_1154_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec_ref(v_as_1145_);
return v_res_1155_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_object* v_00_u03c3_1156_, lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_f_1159_, lean_object* v_keys_1160_, lean_object* v_vals_1161_, lean_object* v_heq_1162_, lean_object* v_i_1163_, lean_object* v_acc_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___redArg(v_f_1159_, v_keys_1160_, v_vals_1161_, v_i_1163_, v_acc_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1159_ = stack[3].m_obj;
lean_object* v_keys_1160_ = stack[4].m_obj;
lean_object* v_vals_1161_ = stack[5].m_obj;
lean_object* v_i_1163_ = stack[7].m_obj;
lean_object* v_acc_1164_ = stack[8].m_obj;
lean_object* v___y_1165_ = stack[9].m_obj;
lean_object* v___y_1166_ = stack[10].m_obj;
lean_object* v___y_1167_ = stack[11].m_obj;
lean_object* v_res_1170_;
v_res_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(lean_box(0), lean_box(0), lean_box(0), v_f_1159_, v_keys_1160_, v_vals_1161_, lean_box(0), v_i_1163_, v_acc_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
stack->m_obj
 = v_res_1170_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11___boxed(lean_object* v_00_u03c3_1171_, lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_f_1174_, lean_object* v_keys_1175_, lean_object* v_vals_1176_, lean_object* v_heq_1177_, lean_object* v_i_1178_, lean_object* v_acc_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forM___at___00Lean_SMap_forM___at___00LeanExport_initState_spec__5_spec__6_spec__7_spec__8_spec__11(v_00_u03c3_1171_, v_00_u03b1_1172_, v_00_u03b2_1173_, v_f_1174_, v_keys_1175_, v_vals_1176_, v_heq_1177_, v_i_1178_, v_acc_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_vals_1176_);
lean_dec_ref(v_keys_1175_);
return v_res_1184_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_x_1188_, lean_object* v_namespaced_1189_, lean_object* v_getM_1190_, lean_object* v_setM_1191_, lean_object* v_rec_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_inc_ref(v_getM_1190_);
lean_inc_ref(v_a_1194_);
v___x_1196_ = lean_apply_1(v_getM_1190_, v_a_1194_);
lean_inc(v_x_1188_);
lean_inc_ref(v_inst_1186_);
lean_inc_ref(v_inst_1187_);
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1187_, v_inst_1186_, v___x_1196_, v_x_1188_);
lean_dec_ref(v___x_1196_);
if (lean_obj_tag(v___x_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_rec_1192_);
lean_dec_ref(v_setM_1191_);
lean_dec_ref(v_getM_1190_);
lean_dec_ref(v_namespaced_1189_);
lean_dec(v_x_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v_val_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1206_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_val_1198_);
lean_ctor_set(v___x_1202_, 1, v_a_1194_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
lean_dec(v___x_1197_);
v___f_1207_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1193_);
v___x_1208_ = lean_apply_3(v_rec_1192_, v_a_1193_, v_a_1194_, lean_box(0));
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v_fst_1210_; lean_object* v_snd_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1243_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v_fst_1210_ = lean_ctor_get(v_a_1209_, 0);
v_snd_1211_ = lean_ctor_get(v_a_1209_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_a_1209_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1213_ = v_a_1209_;
v_isShared_1214_ = v_isSharedCheck_1243_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snd_1211_);
lean_inc(v_fst_1210_);
lean_dec(v_a_1209_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1243_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v_size_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_inc(v_snd_1211_);
v___x_1215_ = lean_apply_1(v_getM_1190_, v_snd_1211_);
v_size_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_n(v_size_1216_, 2);
v___x_1217_ = l_Lean_JsonNumber_fromNat(v_size_1216_);
v___x_1218_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
v___x_1219_ = l_Lean_Json_setObjVal_x21(v_fst_1210_, v_namespaced_1189_, v___x_1218_);
v___x_1220_ = l_Lean_Json_compress(v___x_1219_);
v___x_1221_ = l_IO_println___redArg(v___f_1207_, v___x_1220_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1233_; 
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1234_);
v___x_1223_ = v___x_1221_;
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v___x_1221_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1233_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
lean_inc(v_size_1216_);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1187_, v_inst_1186_, v___x_1215_, v_x_1188_, v_size_1216_);
v___x_1226_ = lean_apply_2(v_setM_1191_, v_snd_1211_, v___x_1225_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 1, v___x_1226_);
lean_ctor_set(v___x_1213_, 0, v_size_1216_);
v___x_1228_ = v___x_1213_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_size_1216_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1230_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1228_);
v___x_1230_ = v___x_1223_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_size_1216_);
lean_dec_ref(v___x_1215_);
lean_del_object(v___x_1213_);
lean_dec(v_snd_1211_);
lean_dec_ref(v_setM_1191_);
lean_dec(v_x_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v_a_1235_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1221_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1221_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
else
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref(v_setM_1191_);
lean_dec_ref(v_getM_1190_);
lean_dec_ref(v_namespaced_1189_);
lean_dec(v_x_1188_);
lean_dec_ref(v_inst_1187_);
lean_dec_ref(v_inst_1186_);
v_a_1244_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1208_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1208_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1186_ = stack[0].m_obj;
lean_object* v_inst_1187_ = stack[1].m_obj;
lean_object* v_x_1188_ = stack[2].m_obj;
lean_object* v_namespaced_1189_ = stack[3].m_obj;
lean_object* v_getM_1190_ = stack[4].m_obj;
lean_object* v_setM_1191_ = stack[5].m_obj;
lean_object* v_rec_1192_ = stack[6].m_obj;
lean_object* v_a_1193_ = stack[7].m_obj;
lean_object* v_a_1194_ = stack[8].m_obj;
lean_object* v_res_1252_;
v_res_1252_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1186_, v_inst_1187_, v_x_1188_, v_namespaced_1189_, v_getM_1190_, v_setM_1191_, v_rec_1192_, v_a_1193_, v_a_1194_);
stack->m_obj
 = v_res_1252_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___boxed(lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_x_1255_, lean_object* v_namespaced_1256_, lean_object* v_getM_1257_, lean_object* v_setM_1258_, lean_object* v_rec_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg(v_inst_1253_, v_inst_1254_, v_x_1255_, v_namespaced_1256_, v_getM_1257_, v_setM_1258_, v_rec_1259_, v_a_1260_, v_a_1261_);
lean_dec_ref(v_a_1260_);
return v_res_1263_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_object* v_00_u03b1_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_x_1267_, lean_object* v_namespaced_1268_, lean_object* v_getM_1269_, lean_object* v_setM_1270_, lean_object* v_rec_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_inc_ref(v_getM_1269_);
lean_inc_ref(v_a_1273_);
v___x_1275_ = lean_apply_1(v_getM_1269_, v_a_1273_);
lean_inc(v_x_1267_);
lean_inc_ref(v_inst_1265_);
lean_inc_ref(v_inst_1266_);
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1266_, v_inst_1265_, v___x_1275_, v_x_1267_);
lean_dec_ref(v___x_1275_);
if (lean_obj_tag(v___x_1276_) == 1)
{
lean_object* v_val_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_rec_1271_);
lean_dec_ref(v_setM_1270_);
lean_dec_ref(v_getM_1269_);
lean_dec_ref(v_namespaced_1268_);
lean_dec(v_x_1267_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
v_val_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_val_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_val_1277_);
lean_ctor_set(v___x_1281_, 1, v_a_1273_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
else
{
lean_object* v___f_1286_; lean_object* v___x_1287_; 
lean_dec(v___x_1276_);
v___f_1286_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_getIdx___redArg___closed__0));
lean_inc_ref(v_a_1272_);
v___x_1287_ = lean_apply_3(v_rec_1271_, v_a_1272_, v_a_1273_, lean_box(0));
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1322_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_fst_1289_ = lean_ctor_get(v_a_1288_, 0);
v_snd_1290_ = lean_ctor_get(v_a_1288_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1292_ = v_a_1288_;
v_isShared_1293_ = v_isSharedCheck_1322_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1290_);
lean_inc(v_fst_1289_);
lean_dec(v_a_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1322_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v_size_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_inc(v_snd_1290_);
v___x_1294_ = lean_apply_1(v_getM_1269_, v_snd_1290_);
v_size_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc_n(v_size_1295_, 2);
v___x_1296_ = l_Lean_JsonNumber_fromNat(v_size_1295_);
v___x_1297_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
v___x_1298_ = l_Lean_Json_setObjVal_x21(v_fst_1289_, v_namespaced_1268_, v___x_1297_);
v___x_1299_ = l_Lean_Json_compress(v___x_1298_);
v___x_1300_ = l_IO_println___redArg(v___f_1286_, v___x_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1312_; 
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; 
v_unused_1313_ = lean_ctor_get(v___x_1300_, 0);
lean_dec(v_unused_1313_);
v___x_1302_ = v___x_1300_;
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v___x_1300_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1312_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
lean_inc(v_size_1295_);
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_1266_, v_inst_1265_, v___x_1294_, v_x_1267_, v_size_1295_);
v___x_1305_ = lean_apply_2(v_setM_1270_, v_snd_1290_, v___x_1304_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1305_);
lean_ctor_set(v___x_1292_, 0, v_size_1295_);
v___x_1307_ = v___x_1292_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_size_1295_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1307_);
v___x_1309_ = v___x_1302_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_size_1295_);
lean_dec_ref(v___x_1294_);
lean_del_object(v___x_1292_);
lean_dec(v_snd_1290_);
lean_dec_ref(v_setM_1270_);
lean_dec(v_x_1267_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
v_a_1314_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1300_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1300_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v_setM_1270_);
lean_dec_ref(v_getM_1269_);
lean_dec_ref(v_namespaced_1268_);
lean_dec(v_x_1267_);
lean_dec_ref(v_inst_1266_);
lean_dec_ref(v_inst_1265_);
v_a_1323_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1287_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1287_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_getIdx_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1265_ = stack[1].m_obj;
lean_object* v_inst_1266_ = stack[2].m_obj;
lean_object* v_x_1267_ = stack[3].m_obj;
lean_object* v_namespaced_1268_ = stack[4].m_obj;
lean_object* v_getM_1269_ = stack[5].m_obj;
lean_object* v_setM_1270_ = stack[6].m_obj;
lean_object* v_rec_1271_ = stack[7].m_obj;
lean_object* v_a_1272_ = stack[8].m_obj;
lean_object* v_a_1273_ = stack[9].m_obj;
lean_object* v_res_1331_;
v_res_1331_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(lean_box(0), v_inst_1265_, v_inst_1266_, v_x_1267_, v_namespaced_1268_, v_getM_1269_, v_setM_1270_, v_rec_1271_, v_a_1272_, v_a_1273_);
stack->m_obj
 = v_res_1331_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_getIdx___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_x_1335_, lean_object* v_namespaced_1336_, lean_object* v_getM_1337_, lean_object* v_setM_1338_, lean_object* v_rec_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_LeanExport_Basic_0__LeanExport_getIdx(v_00_u03b1_1332_, v_inst_1333_, v_inst_1334_, v_x_1335_, v_namespaced_1336_, v_getM_1337_, v_setM_1338_, v_rec_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1343_;
}
}
static lean_object* _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_instMonadEIO___redArg();
return v___x_1344_;
}
}
lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; lean_object* v___f_1350_; lean_object* v___f_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___f_1362_; lean_object* v___x_1423__overap_1363_; lean_object* v___x_1364_; 
v___x_1349_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_1350_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1350_, 0, v___x_1349_);
v___f_1351_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1351_, 0, v___x_1349_);
v___f_1352_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_1352_, 0, v___x_1349_);
v___f_1353_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_1353_, 0, v___x_1349_);
v___x_1354_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_1354_, 0, lean_box(0));
lean_closure_set(v___x_1354_, 1, lean_box(0));
lean_closure_set(v___x_1354_, 2, v___x_1349_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v___f_1350_);
v___x_1356_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_1356_, 0, lean_box(0));
lean_closure_set(v___x_1356_, 1, lean_box(0));
lean_closure_set(v___x_1356_, 2, v___x_1349_);
v___x_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
lean_ctor_set(v___x_1357_, 2, v___f_1351_);
lean_ctor_set(v___x_1357_, 3, v___f_1352_);
lean_ctor_set(v___x_1357_, 4, v___f_1353_);
v___x_1358_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_1358_, 0, lean_box(0));
lean_closure_set(v___x_1358_, 1, lean_box(0));
lean_closure_set(v___x_1358_, 2, v___x_1349_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1357_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_box(0);
v___x_1361_ = l_instInhabitedOfMonad___redArg(v___x_1359_, v___x_1360_);
v___f_1362_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1362_, 0, v___x_1361_);
v___x_1423__overap_1363_ = lean_panic_fn_borrowed(v___f_1362_, v_msg_1345_);
lean_dec_ref(v___f_1362_);
lean_inc_ref(v___y_1346_);
v___x_1364_ = lean_apply_3(v___x_1423__overap_1363_, v___y_1346_, v___y_1347_, lean_box(0));
return v___x_1364_;
}
}
LEAN_EXPORT void l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1345_ = stack[0].m_obj;
lean_object* v___y_1346_ = stack[1].m_obj;
lean_object* v___y_1347_ = stack[2].m_obj;
lean_object* v_res_1365_;
v_res_1365_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1345_, v___y_1346_, v___y_1347_);
stack->m_obj
 = v_res_1365_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___boxed(lean_object* v_msg_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v_msg_1366_, v___y_1367_, v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(lean_object* v_a_1371_, lean_object* v_x_1372_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 0)
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_box(0);
return v___x_1373_;
}
else
{
lean_object* v_key_1374_; lean_object* v_value_1375_; lean_object* v_tail_1376_; uint8_t v___x_1377_; 
v_key_1374_ = lean_ctor_get(v_x_1372_, 0);
v_value_1375_ = lean_ctor_get(v_x_1372_, 1);
v_tail_1376_ = lean_ctor_get(v_x_1372_, 2);
v___x_1377_ = lean_name_eq(v_key_1374_, v_a_1371_);
if (v___x_1377_ == 0)
{
v_x_1372_ = v_tail_1376_;
goto _start;
}
else
{
lean_object* v___x_1379_; 
lean_inc(v_value_1375_);
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_value_1375_);
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg___boxed(lean_object* v_a_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1380_, v_x_1381_);
lean_dec(v_x_1381_);
lean_dec(v_a_1380_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(lean_object* v_m_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_buckets_1385_; lean_object* v___x_1386_; uint64_t v___y_1388_; 
v_buckets_1385_ = lean_ctor_get(v_m_1383_, 1);
v___x_1386_ = lean_array_get_size(v_buckets_1385_);
if (lean_obj_tag(v_a_1384_) == 0)
{
uint64_t v___x_1402_; 
v___x_1402_ = 1723ULL;
v___y_1388_ = v___x_1402_;
goto v___jp_1387_;
}
else
{
uint64_t v_hash_1403_; 
v_hash_1403_ = lean_ctor_get_uint64(v_a_1384_, sizeof(void*)*2);
v___y_1388_ = v_hash_1403_;
goto v___jp_1387_;
}
v___jp_1387_:
{
uint64_t v___x_1389_; uint64_t v___x_1390_; uint64_t v_fold_1391_; uint64_t v___x_1392_; uint64_t v___x_1393_; uint64_t v___x_1394_; size_t v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; size_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1389_ = 32ULL;
v___x_1390_ = lean_uint64_shift_right(v___y_1388_, v___x_1389_);
v_fold_1391_ = lean_uint64_xor(v___y_1388_, v___x_1390_);
v___x_1392_ = 16ULL;
v___x_1393_ = lean_uint64_shift_right(v_fold_1391_, v___x_1392_);
v___x_1394_ = lean_uint64_xor(v_fold_1391_, v___x_1393_);
v___x_1395_ = lean_uint64_to_usize(v___x_1394_);
v___x_1396_ = lean_usize_of_nat(v___x_1386_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_sub(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_usize_land(v___x_1395_, v___x_1398_);
v___x_1400_ = lean_array_uget_borrowed(v_buckets_1385_, v___x_1399_);
v___x_1401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1384_, v___x_1400_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg___boxed(lean_object* v_m_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1404_, v_a_1405_);
lean_dec(v_a_1405_);
lean_dec_ref(v_m_1404_);
return v_res_1406_;
}
}
lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(lean_object* v_s_1407_){
_start:
{
lean_object* v___x_1409_; lean_object* v_putStr_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_get_stdout();
v_putStr_1410_ = lean_ctor_get(v___x_1409_, 4);
lean_inc_ref(v_putStr_1410_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = lean_apply_2(v_putStr_1410_, v_s_1407_, lean_box(0));
return v___x_1411_;
}
}
LEAN_EXPORT void l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1407_ = stack[0].m_obj;
lean_object* v_res_1412_;
v_res_1412_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1407_);
stack->m_obj
 = v_res_1412_;
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2___boxed(lean_object* v_s_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v_s_1413_);
return v_res_1415_;
}
}
lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(lean_object* v_s_1416_){
_start:
{
uint32_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = 10;
v___x_1419_ = lean_string_push(v_s_1416_, v___x_1418_);
v___x_1420_ = l_IO_print___at___00IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_spec__2(v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT void l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1416_ = stack[0].m_obj;
lean_object* v_res_1421_;
v_res_1421_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1416_);
stack->m_obj
 = v_res_1421_;
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1___boxed(lean_object* v_s_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v_s_1422_);
return v_res_1424_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1430_ = lean_unsigned_to_nat(18u);
v___x_1431_ = lean_unsigned_to_nat(114u);
v___x_1432_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__2));
v___x_1433_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1434_ = l_mkPanicMessageWithDecl(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_);
return v___x_1434_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName(lean_object* v_n_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_visitedNames_1443_; lean_object* v___x_1444_; 
v_visitedNames_1443_ = lean_ctor_get(v_a_1441_, 0);
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_visitedNames_1443_, v_n_1439_);
if (lean_obj_tag(v___x_1444_) == 1)
{
lean_object* v_val_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v_n_1439_);
v_val_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_val_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v_val_1445_);
lean_ctor_set(v___x_1449_, 1, v_a_1441_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set_tag(v___x_1447_, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
lean_object* v___x_1454_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; 
lean_dec(v___x_1444_);
v___x_1454_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__0));
switch(lean_obj_tag(v_n_1439_))
{
case 0:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4, &l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__4);
v___x_1499_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1498_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v_fst_1501_ = lean_ctor_get(v_a_1500_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v_a_1500_, 1);
lean_inc(v_snd_1502_);
lean_dec(v_a_1500_);
v_fst_1456_ = v_fst_1501_;
v_snd_1457_ = v_snd_1502_;
goto v___jp_1455_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1499_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1499_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
case 1:
{
lean_object* v_pre_1511_; lean_object* v_str_1512_; lean_object* v___x_1513_; 
v_pre_1511_ = lean_ctor_get(v_n_1439_, 0);
v_str_1512_ = lean_ctor_get(v_n_1439_, 1);
lean_inc(v_pre_1511_);
v___x_1513_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1511_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1542_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1542_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v_fst_1518_; lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1541_; 
v_fst_1518_ = lean_ctor_get(v_a_1514_, 0);
v_snd_1519_ = lean_ctor_get(v_a_1514_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1521_ = v_a_1514_;
v_isShared_1522_ = v_isSharedCheck_1541_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_inc(v_fst_1518_);
lean_dec(v_a_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1541_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1523_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__5));
v___x_1524_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1525_ = l_Lean_JsonNumber_fromNat(v_fst_1518_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set_tag(v___x_1516_, 2);
lean_ctor_set(v___x_1516_, 0, v___x_1525_);
v___x_1527_ = v___x_1516_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1529_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1527_);
lean_ctor_set(v___x_1521_, 0, v___x_1524_);
v___x_1529_ = v___x_1521_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_inc_ref(v_str_1512_);
v___x_1530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_str_1512_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1523_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1529_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = l_Lean_Json_mkObj(v___x_1534_);
lean_dec_ref_known(v___x_1534_, 2);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1523_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v___x_1532_);
v___x_1538_ = l_Lean_Json_mkObj(v___x_1537_);
lean_dec_ref_known(v___x_1537_, 2);
v_fst_1456_ = v___x_1538_;
v_snd_1457_ = v_snd_1519_;
goto v___jp_1455_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1439_, 2);
return v___x_1513_;
}
}
default: 
{
lean_object* v_pre_1543_; lean_object* v_i_1544_; lean_object* v___x_1545_; 
v_pre_1543_ = lean_ctor_get(v_n_1439_, 0);
v_i_1544_ = lean_ctor_get(v_n_1439_, 1);
lean_inc(v_pre_1543_);
v___x_1545_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_pre_1543_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1576_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1576_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1576_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v_fst_1550_; lean_object* v_snd_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1575_; 
v_fst_1550_ = lean_ctor_get(v_a_1546_, 0);
v_snd_1551_ = lean_ctor_get(v_a_1546_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_a_1546_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1553_ = v_a_1546_;
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snd_1551_);
lean_inc(v_fst_1550_);
lean_dec(v_a_1546_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1575_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1555_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__7));
v___x_1556_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__6));
v___x_1557_ = l_Lean_JsonNumber_fromNat(v_fst_1550_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 2);
lean_ctor_set(v___x_1548_, 0, v___x_1557_);
v___x_1559_ = v___x_1548_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___x_1559_);
lean_ctor_set(v___x_1553_, 0, v___x_1556_);
v___x_1561_ = v___x_1553_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1562_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__8));
lean_inc(v_i_1544_);
v___x_1563_ = l_Lean_JsonNumber_fromNat(v_i_1544_);
v___x_1564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1561_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_Json_mkObj(v___x_1568_);
lean_dec_ref_known(v___x_1568_, 2);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1555_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1566_);
v___x_1572_ = l_Lean_Json_mkObj(v___x_1571_);
lean_dec_ref_known(v___x_1571_, 2);
v_fst_1456_ = v___x_1572_;
v_snd_1457_ = v_snd_1551_;
goto v___jp_1455_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_n_1439_, 2);
return v___x_1545_;
}
}
}
v___jp_1455_:
{
lean_object* v_visitedNames_1458_; lean_object* v_visitedLevels_1459_; lean_object* v_visitedExprs_1460_; lean_object* v_visitedConstants_1461_; lean_object* v_noMDataExprs_1462_; uint8_t v_exportMData_1463_; uint8_t v_exportUnsafe_1464_; uint8_t v_ignoreMissing_1465_; lean_object* v_recursorMap_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1497_; 
v_visitedNames_1458_ = lean_ctor_get(v_snd_1457_, 0);
v_visitedLevels_1459_ = lean_ctor_get(v_snd_1457_, 1);
v_visitedExprs_1460_ = lean_ctor_get(v_snd_1457_, 2);
v_visitedConstants_1461_ = lean_ctor_get(v_snd_1457_, 3);
v_noMDataExprs_1462_ = lean_ctor_get(v_snd_1457_, 4);
v_exportMData_1463_ = lean_ctor_get_uint8(v_snd_1457_, sizeof(void*)*6);
v_exportUnsafe_1464_ = lean_ctor_get_uint8(v_snd_1457_, sizeof(void*)*6 + 1);
v_ignoreMissing_1465_ = lean_ctor_get_uint8(v_snd_1457_, sizeof(void*)*6 + 2);
v_recursorMap_1466_ = lean_ctor_get(v_snd_1457_, 5);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_snd_1457_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1468_ = v_snd_1457_;
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_recursorMap_1466_);
lean_inc(v_noMDataExprs_1462_);
lean_inc(v_visitedConstants_1461_);
lean_inc(v_visitedExprs_1460_);
lean_inc(v_visitedLevels_1459_);
lean_inc(v_visitedNames_1458_);
lean_dec(v_snd_1457_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1497_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_size_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_size_1470_ = lean_ctor_get(v_visitedNames_1458_, 0);
lean_inc_n(v_size_1470_, 2);
v___x_1471_ = l_Lean_JsonNumber_fromNat(v_size_1470_);
v___x_1472_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
v___x_1473_ = l_Lean_Json_setObjVal_x21(v_fst_1456_, v___x_1454_, v___x_1472_);
v___x_1474_ = l_Lean_Json_compress(v___x_1473_);
v___x_1475_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1474_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1487_; 
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1475_, 0);
lean_dec(v_unused_1488_);
v___x_1477_ = v___x_1475_;
v_isShared_1478_ = v_isSharedCheck_1487_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v___x_1475_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1487_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_inc(v_size_1470_);
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__0___redArg(v_visitedNames_1458_, v_n_1439_, v_size_1470_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1479_);
v___x_1481_ = v___x_1468_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_visitedLevels_1459_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_visitedExprs_1460_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_visitedConstants_1461_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_noMDataExprs_1462_);
lean_ctor_set(v_reuseFailAlloc_1486_, 5, v_recursorMap_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*6, v_exportMData_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*6 + 1, v_exportUnsafe_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*6 + 2, v_ignoreMissing_1465_);
v___x_1481_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_size_1470_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1482_);
v___x_1484_ = v___x_1477_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_size_1470_);
lean_del_object(v___x_1468_);
lean_dec(v_recursorMap_1466_);
lean_dec_ref(v_noMDataExprs_1462_);
lean_dec_ref(v_visitedConstants_1461_);
lean_dec_ref(v_visitedExprs_1460_);
lean_dec_ref(v_visitedLevels_1459_);
lean_dec_ref(v_visitedNames_1458_);
lean_dec(v_n_1439_);
v_a_1489_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1475_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1475_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpName_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1439_ = stack[0].m_obj;
lean_object* v_a_1440_ = stack[1].m_obj;
lean_object* v_a_1441_ = stack[2].m_obj;
lean_object* v_res_1577_;
v_res_1577_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1439_, v_a_1440_, v_a_1441_);
stack->m_obj
 = v_res_1577_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpName___boxed(lean_object* v_n_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_n_1578_, v_a_1579_, v_a_1580_);
lean_dec_ref(v_a_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(lean_object* v_00_u03b2_1583_, lean_object* v_m_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___redArg(v_m_1584_, v_a_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0___boxed(lean_object* v_00_u03b2_1587_, lean_object* v_m_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0(v_00_u03b2_1587_, v_m_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_m_1588_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(lean_object* v_00_u03b2_1591_, lean_object* v_a_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___redArg(v_a_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1595_, lean_object* v_a_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__0_spec__0(v_00_u03b2_1595_, v_a_1596_, v_x_1597_);
lean_dec(v_x_1597_);
lean_dec(v_a_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(lean_object* v_a_1599_, lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_box(0);
return v___x_1601_;
}
else
{
lean_object* v_key_1602_; lean_object* v_value_1603_; lean_object* v_tail_1604_; uint8_t v___x_1605_; 
v_key_1602_ = lean_ctor_get(v_x_1600_, 0);
v_value_1603_ = lean_ctor_get(v_x_1600_, 1);
v_tail_1604_ = lean_ctor_get(v_x_1600_, 2);
v___x_1605_ = lean_level_eq(v_key_1602_, v_a_1599_);
if (v___x_1605_ == 0)
{
v_x_1600_ = v_tail_1604_;
goto _start;
}
else
{
lean_object* v___x_1607_; 
lean_inc(v_value_1603_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v_value_1603_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg___boxed(lean_object* v_a_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1608_, v_x_1609_);
lean_dec(v_x_1609_);
lean_dec(v_a_1608_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(lean_object* v_m_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_buckets_1613_; lean_object* v___x_1614_; uint64_t v___x_1615_; uint64_t v___x_1616_; uint64_t v___x_1617_; uint64_t v_fold_1618_; uint64_t v___x_1619_; uint64_t v___x_1620_; uint64_t v___x_1621_; size_t v___x_1622_; size_t v___x_1623_; size_t v___x_1624_; size_t v___x_1625_; size_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_buckets_1613_ = lean_ctor_get(v_m_1611_, 1);
v___x_1614_ = lean_array_get_size(v_buckets_1613_);
v___x_1615_ = l_Lean_Level_hash(v_a_1612_);
v___x_1616_ = 32ULL;
v___x_1617_ = lean_uint64_shift_right(v___x_1615_, v___x_1616_);
v_fold_1618_ = lean_uint64_xor(v___x_1615_, v___x_1617_);
v___x_1619_ = 16ULL;
v___x_1620_ = lean_uint64_shift_right(v_fold_1618_, v___x_1619_);
v___x_1621_ = lean_uint64_xor(v_fold_1618_, v___x_1620_);
v___x_1622_ = lean_uint64_to_usize(v___x_1621_);
v___x_1623_ = lean_usize_of_nat(v___x_1614_);
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = lean_usize_sub(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_usize_land(v___x_1622_, v___x_1625_);
v___x_1627_ = lean_array_uget_borrowed(v_buckets_1613_, v___x_1626_);
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1612_, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg___boxed(lean_object* v_m_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1629_, v_a_1630_);
lean_dec(v_a_1630_);
lean_dec_ref(v_m_1629_);
return v_res_1631_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1638_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_1639_ = lean_unsigned_to_nat(23u);
v___x_1640_ = lean_unsigned_to_nat(132u);
v___x_1641_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__5));
v___x_1642_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_1643_ = l_mkPanicMessageWithDecl(v___x_1642_, v___x_1641_, v___x_1640_, v___x_1639_, v___x_1638_);
return v___x_1643_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel(lean_object* v_l_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_visitedLevels_1648_; lean_object* v___x_1649_; 
v_visitedLevels_1648_ = lean_ctor_get(v_a_1646_, 1);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_visitedLevels_1648_, v_l_1644_);
if (lean_obj_tag(v___x_1649_) == 1)
{
lean_object* v_val_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_l_1644_);
v_val_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_val_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_val_1650_);
lean_ctor_set(v___x_1654_, 1, v_a_1646_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v_fst_1661_; lean_object* v_snd_1662_; 
lean_dec(v___x_1649_);
v___x_1659_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__0));
switch(lean_obj_tag(v_l_1644_))
{
case 1:
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v_l_1644_, 0);
lean_inc(v_a_1703_);
v___x_1704_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1703_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1726_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1726_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1726_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1725_; 
v_fst_1709_ = lean_ctor_get(v_a_1705_, 0);
v_snd_1710_ = lean_ctor_get(v_a_1705_, 1);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_a_1705_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1712_ = v_a_1705_;
v_isShared_1713_ = v_isSharedCheck_1725_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snd_1710_);
lean_inc(v_fst_1709_);
lean_dec(v_a_1705_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1725_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1714_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__1));
v___x_1715_ = l_Lean_JsonNumber_fromNat(v_fst_1709_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 2);
lean_ctor_set(v___x_1707_, 0, v___x_1715_);
v___x_1717_ = v___x_1707_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1717_);
lean_ctor_set(v___x_1712_, 0, v___x_1714_);
v___x_1719_ = v___x_1712_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_box(0);
v___x_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1719_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = l_Lean_Json_mkObj(v___x_1721_);
lean_dec_ref_known(v___x_1721_, 2);
v_fst_1661_ = v___x_1722_;
v_snd_1662_ = v_snd_1710_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1644_, 1);
return v___x_1704_;
}
}
case 2:
{
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1727_ = lean_ctor_get(v_l_1644_, 0);
v_a_1728_ = lean_ctor_get(v_l_1644_, 1);
lean_inc(v_a_1727_);
v___x_1729_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1727_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1774_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1774_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1774_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_fst_1734_; lean_object* v_snd_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1773_; 
v_fst_1734_ = lean_ctor_get(v_a_1730_, 0);
v_snd_1735_ = lean_ctor_get(v_a_1730_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1730_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1737_ = v_a_1730_;
v_isShared_1738_ = v_isSharedCheck_1773_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snd_1735_);
lean_inc(v_fst_1734_);
lean_dec(v_a_1730_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1773_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; 
lean_inc(v_a_1728_);
v___x_1739_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1728_, v_a_1645_, v_snd_1735_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1772_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1742_ = v___x_1739_;
v_isShared_1743_ = v_isSharedCheck_1772_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1739_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1772_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v_fst_1744_; lean_object* v_snd_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1771_; 
v_fst_1744_ = lean_ctor_get(v_a_1740_, 0);
v_snd_1745_ = lean_ctor_get(v_a_1740_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1740_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1747_ = v_a_1740_;
v_isShared_1748_ = v_isSharedCheck_1771_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_snd_1745_);
lean_inc(v_fst_1744_);
lean_dec(v_a_1740_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1771_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__2));
v___x_1750_ = l_Lean_JsonNumber_fromNat(v_fst_1734_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 2);
lean_ctor_set(v___x_1742_, 0, v___x_1750_);
v___x_1752_ = v___x_1742_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = l_Lean_JsonNumber_fromNat(v_fst_1744_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set_tag(v___x_1732_, 2);
lean_ctor_set(v___x_1732_, 0, v___x_1753_);
v___x_1755_ = v___x_1732_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1756_ = lean_unsigned_to_nat(2u);
v___x_1757_ = lean_mk_empty_array_with_capacity(v___x_1756_);
v___x_1758_ = lean_array_push(v___x_1757_, v___x_1752_);
v___x_1759_ = lean_array_push(v___x_1758_, v___x_1755_);
v___x_1760_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v___x_1760_);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1762_ = v___x_1747_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_box(0);
if (v_isShared_1738_ == 0)
{
lean_ctor_set_tag(v___x_1737_, 1);
lean_ctor_set(v___x_1737_, 1, v___x_1763_);
lean_ctor_set(v___x_1737_, 0, v___x_1762_);
v___x_1765_ = v___x_1737_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Json_mkObj(v___x_1765_);
lean_dec_ref(v___x_1765_);
v_fst_1661_ = v___x_1766_;
v_snd_1662_ = v_snd_1745_;
goto v___jp_1660_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1737_);
lean_dec(v_fst_1734_);
lean_del_object(v___x_1732_);
lean_dec_ref_known(v_l_1644_, 2);
return v___x_1739_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1644_, 2);
return v___x_1729_;
}
}
case 3:
{
lean_object* v_a_1775_; lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1775_ = lean_ctor_get(v_l_1644_, 0);
v_a_1776_ = lean_ctor_get(v_l_1644_, 1);
lean_inc(v_a_1775_);
v___x_1777_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1775_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1822_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1822_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1822_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_fst_1782_; lean_object* v_snd_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1821_; 
v_fst_1782_ = lean_ctor_get(v_a_1778_, 0);
v_snd_1783_ = lean_ctor_get(v_a_1778_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_a_1778_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1785_ = v_a_1778_;
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snd_1783_);
lean_inc(v_fst_1782_);
lean_dec(v_a_1778_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1821_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; 
lean_inc(v_a_1776_);
v___x_1787_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_a_1776_, v_a_1645_, v_snd_1783_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1820_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1820_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1820_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_fst_1792_; lean_object* v_snd_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1819_; 
v_fst_1792_ = lean_ctor_get(v_a_1788_, 0);
v_snd_1793_ = lean_ctor_get(v_a_1788_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1795_ = v_a_1788_;
v_isShared_1796_ = v_isSharedCheck_1819_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1792_);
lean_dec(v_a_1788_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1819_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1797_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__3));
v___x_1798_ = l_Lean_JsonNumber_fromNat(v_fst_1782_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set_tag(v___x_1790_, 2);
lean_ctor_set(v___x_1790_, 0, v___x_1798_);
v___x_1800_ = v___x_1790_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = l_Lean_JsonNumber_fromNat(v_fst_1792_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set_tag(v___x_1780_, 2);
lean_ctor_set(v___x_1780_, 0, v___x_1801_);
v___x_1803_ = v___x_1780_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1804_ = lean_unsigned_to_nat(2u);
v___x_1805_ = lean_mk_empty_array_with_capacity(v___x_1804_);
v___x_1806_ = lean_array_push(v___x_1805_, v___x_1800_);
v___x_1807_ = lean_array_push(v___x_1806_, v___x_1803_);
v___x_1808_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 1, v___x_1808_);
lean_ctor_set(v___x_1795_, 0, v___x_1797_);
v___x_1810_ = v___x_1795_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_box(0);
if (v_isShared_1786_ == 0)
{
lean_ctor_set_tag(v___x_1785_, 1);
lean_ctor_set(v___x_1785_, 1, v___x_1811_);
lean_ctor_set(v___x_1785_, 0, v___x_1810_);
v___x_1813_ = v___x_1785_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Json_mkObj(v___x_1813_);
lean_dec_ref(v___x_1813_);
v_fst_1661_ = v___x_1814_;
v_snd_1662_ = v_snd_1793_;
goto v___jp_1660_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1785_);
lean_dec(v_fst_1782_);
lean_del_object(v___x_1780_);
lean_dec_ref_known(v_l_1644_, 2);
return v___x_1787_;
}
}
}
}
else
{
lean_dec_ref_known(v_l_1644_, 2);
return v___x_1777_;
}
}
case 4:
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v_l_1644_, 0);
lean_inc(v_a_1823_);
v___x_1824_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_a_1823_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1846_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1846_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1845_; 
v_fst_1829_ = lean_ctor_get(v_a_1825_, 0);
v_snd_1830_ = lean_ctor_get(v_a_1825_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1832_ = v_a_1825_;
v_isShared_1833_ = v_isSharedCheck_1845_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v_a_1825_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1845_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__4));
v___x_1835_ = l_Lean_JsonNumber_fromNat(v_fst_1829_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 2);
lean_ctor_set(v___x_1827_, 0, v___x_1835_);
v___x_1837_ = v___x_1827_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1837_);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_Json_mkObj(v___x_1841_);
lean_dec_ref_known(v___x_1841_, 2);
v_fst_1661_ = v___x_1842_;
v_snd_1662_ = v_snd_1830_;
goto v___jp_1660_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_l_1644_, 1);
return v___x_1824_;
}
}
default: 
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6, &l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_dumpLevel___closed__6);
v___x_1848_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_1847_, v_a_1645_, v_a_1646_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v_fst_1850_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_fst_1850_);
v_snd_1851_ = lean_ctor_get(v_a_1849_, 1);
lean_inc(v_snd_1851_);
lean_dec(v_a_1849_);
v_fst_1661_ = v_fst_1850_;
v_snd_1662_ = v_snd_1851_;
goto v___jp_1660_;
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec(v_l_1644_);
v_a_1852_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1848_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
v___jp_1660_:
{
lean_object* v_visitedLevels_1663_; lean_object* v_visitedNames_1664_; lean_object* v_visitedExprs_1665_; lean_object* v_visitedConstants_1666_; lean_object* v_noMDataExprs_1667_; uint8_t v_exportMData_1668_; uint8_t v_exportUnsafe_1669_; uint8_t v_ignoreMissing_1670_; lean_object* v_recursorMap_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1702_; 
v_visitedLevels_1663_ = lean_ctor_get(v_snd_1662_, 1);
v_visitedNames_1664_ = lean_ctor_get(v_snd_1662_, 0);
v_visitedExprs_1665_ = lean_ctor_get(v_snd_1662_, 2);
v_visitedConstants_1666_ = lean_ctor_get(v_snd_1662_, 3);
v_noMDataExprs_1667_ = lean_ctor_get(v_snd_1662_, 4);
v_exportMData_1668_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6);
v_exportUnsafe_1669_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6 + 1);
v_ignoreMissing_1670_ = lean_ctor_get_uint8(v_snd_1662_, sizeof(void*)*6 + 2);
v_recursorMap_1671_ = lean_ctor_get(v_snd_1662_, 5);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_snd_1662_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1673_ = v_snd_1662_;
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_recursorMap_1671_);
lean_inc(v_noMDataExprs_1667_);
lean_inc(v_visitedConstants_1666_);
lean_inc(v_visitedExprs_1665_);
lean_inc(v_visitedLevels_1663_);
lean_inc(v_visitedNames_1664_);
lean_dec(v_snd_1662_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1702_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_size_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_size_1675_ = lean_ctor_get(v_visitedLevels_1663_, 0);
lean_inc_n(v_size_1675_, 2);
v___x_1676_ = l_Lean_JsonNumber_fromNat(v_size_1675_);
v___x_1677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
v___x_1678_ = l_Lean_Json_setObjVal_x21(v_fst_1661_, v___x_1659_, v___x_1677_);
v___x_1679_ = l_Lean_Json_compress(v___x_1678_);
v___x_1680_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1692_; 
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1680_, 0);
lean_dec(v_unused_1693_);
v___x_1682_ = v___x_1680_;
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
else
{
lean_dec(v___x_1680_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1692_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_inc(v_size_1675_);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00LeanExport_M_run_spec__1___redArg(v_visitedLevels_1663_, v_l_1644_, v_size_1675_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 1, v___x_1684_);
v___x_1686_ = v___x_1673_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_visitedNames_1664_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_visitedExprs_1665_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_visitedConstants_1666_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_noMDataExprs_1667_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v_recursorMap_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6, v_exportMData_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6 + 1, v_exportUnsafe_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*6 + 2, v_ignoreMissing_1670_);
v___x_1686_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v_size_1675_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1687_);
v___x_1689_ = v___x_1682_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_size_1675_);
lean_del_object(v___x_1673_);
lean_dec(v_recursorMap_1671_);
lean_dec_ref(v_noMDataExprs_1667_);
lean_dec_ref(v_visitedConstants_1666_);
lean_dec_ref(v_visitedExprs_1665_);
lean_dec_ref(v_visitedNames_1664_);
lean_dec_ref(v_visitedLevels_1663_);
lean_dec(v_l_1644_);
v_a_1694_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1680_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1680_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_1644_ = stack[0].m_obj;
lean_object* v_a_1645_ = stack[1].m_obj;
lean_object* v_a_1646_ = stack[2].m_obj;
lean_object* v_res_1860_;
v_res_1860_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1644_, v_a_1645_, v_a_1646_);
stack->m_obj
 = v_res_1860_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpLevel___boxed(lean_object* v_l_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_l_1861_, v_a_1862_, v_a_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(lean_object* v_00_u03b2_1866_, lean_object* v_m_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___redArg(v_m_1867_, v_a_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0___boxed(lean_object* v_00_u03b2_1870_, lean_object* v_m_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0(v_00_u03b2_1870_, v_m_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_m_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(lean_object* v_00_u03b2_1874_, lean_object* v_a_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___redArg(v_a_1875_, v_x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1878_, lean_object* v_a_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_dumpLevel_spec__0_spec__0(v_00_u03b2_1878_, v_a_1879_, v_x_1880_);
lean_dec(v_x_1880_);
lean_dec(v_a_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
if (lean_obj_tag(v_a_1882_) == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = l_List_reverse___redArg(v_a_1883_);
return v___x_1884_;
}
else
{
lean_object* v_head_1885_; lean_object* v_tail_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1895_; 
v_head_1885_ = lean_ctor_get(v_a_1882_, 0);
v_tail_1886_ = lean_ctor_get(v_a_1882_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_a_1882_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1888_ = v_a_1882_;
v_isShared_1889_ = v_isSharedCheck_1895_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_tail_1886_);
lean_inc(v_head_1885_);
lean_dec(v_a_1882_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1895_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_Level_param___override(v_head_1885_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_a_1883_);
lean_ctor_set(v___x_1888_, 0, v___x_1890_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_a_1883_);
v___x_1892_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
v_a_1882_ = v_tail_1886_;
v_a_1883_ = v___x_1892_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(size_t v_sz_1896_, size_t v_i_1897_, lean_object* v_bs_1898_){
_start:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_usize_dec_lt(v_i_1897_, v_sz_1896_);
if (v___x_1899_ == 0)
{
return v_bs_1898_;
}
else
{
lean_object* v_v_1900_; lean_object* v___x_1901_; lean_object* v_bs_x27_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; 
v_v_1900_ = lean_array_uget(v_bs_1898_, v_i_1897_);
v___x_1901_ = lean_unsigned_to_nat(0u);
v_bs_x27_1902_ = lean_array_uset(v_bs_1898_, v_i_1897_, v___x_1901_);
v___x_1903_ = l_Lean_JsonNumber_fromNat(v_v_1900_);
v___x_1904_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1897_, v___x_1905_);
v___x_1907_ = lean_array_uset(v_bs_x27_1902_, v_i_1897_, v___x_1904_);
v_i_1897_ = v___x_1906_;
v_bs_1898_ = v___x_1907_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1896_ = stack[0].m_num;
size_t v_i_1897_ = stack[1].m_num;
lean_object* v_bs_1898_ = stack[2].m_obj;
lean_object* v_res_1909_;
v_res_1909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1896_, v_i_1897_, v_bs_1898_);
stack->m_obj
 = v_res_1909_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1910_, lean_object* v_i_1911_, lean_object* v_bs_1912_){
_start:
{
size_t v_sz_boxed_1913_; size_t v_i_boxed_1914_; lean_object* v_res_1915_; 
v_sz_boxed_1913_ = lean_unbox_usize(v_sz_1910_);
lean_dec(v_sz_1910_);
v_i_boxed_1914_ = lean_unbox_usize(v_i_1911_);
lean_dec(v_i_1911_);
v_res_1915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_boxed_1913_, v_i_boxed_1914_, v_bs_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(lean_object* v_a_1916_){
_start:
{
size_t v_sz_1917_; size_t v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_sz_1917_ = lean_array_size(v_a_1916_);
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3_spec__4(v_sz_1917_, v___x_1918_, v_a_1916_);
v___x_1920_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_array_mk(v_a_1921_);
v___x_1923_ = l_Lean_Array_toJson___at___00Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3_spec__3(v___x_1922_);
return v___x_1923_;
}
}
lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(lean_object* v_x_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
if (lean_obj_tag(v_x_1924_) == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = l_List_reverse___redArg(v_x_1925_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v___y_1927_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
return v___x_1931_;
}
else
{
lean_object* v_head_1932_; lean_object* v_tail_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1953_; 
v_head_1932_ = lean_ctor_get(v_x_1924_, 0);
v_tail_1933_ = lean_ctor_get(v_x_1924_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1924_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1935_ = v_x_1924_;
v_isShared_1936_ = v_isSharedCheck_1953_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_tail_1933_);
lean_inc(v_head_1932_);
lean_dec(v_x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1953_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; 
v___x_1937_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_head_1932_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v_fst_1939_; lean_object* v_snd_1940_; lean_object* v___x_1942_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v_fst_1939_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_fst_1939_);
v_snd_1940_ = lean_ctor_get(v_a_1938_, 1);
lean_inc(v_snd_1940_);
lean_dec(v_a_1938_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_x_1925_);
lean_ctor_set(v___x_1935_, 0, v_fst_1939_);
v___x_1942_ = v___x_1935_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_fst_1939_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_x_1925_);
v___x_1942_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
v_x_1924_ = v_tail_1933_;
v_x_1925_ = v___x_1942_;
v___y_1927_ = v_snd_1940_;
goto _start;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1935_);
lean_dec(v_tail_1933_);
lean_dec(v_x_1925_);
v_a_1945_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1937_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1937_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1924_ = stack[0].m_obj;
lean_object* v_x_1925_ = stack[1].m_obj;
lean_object* v___y_1926_ = stack[2].m_obj;
lean_object* v___y_1927_ = stack[3].m_obj;
lean_object* v_res_1954_;
v_res_1954_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1924_, v_x_1925_, v___y_1926_, v___y_1927_);
stack->m_obj
 = v_res_1954_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2___boxed(lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_x_1955_, v_x_1956_, v___y_1957_, v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1960_;
}
}
lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = l_List_reverse___redArg(v_x_1962_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v___y_1964_);
v___x_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
return v___x_1968_;
}
else
{
lean_object* v_head_1969_; lean_object* v_tail_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1990_; 
v_head_1969_ = lean_ctor_get(v_x_1961_, 0);
v_tail_1970_ = lean_ctor_get(v_x_1961_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1972_ = v_x_1961_;
v_isShared_1973_ = v_isSharedCheck_1990_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_tail_1970_);
lean_inc(v_head_1969_);
lean_dec(v_x_1961_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1990_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; 
v___x_1974_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_head_1969_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1979_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v_fst_1976_ = lean_ctor_get(v_a_1975_, 0);
lean_inc(v_fst_1976_);
v_snd_1977_ = lean_ctor_get(v_a_1975_, 1);
lean_inc(v_snd_1977_);
lean_dec(v_a_1975_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v_x_1962_);
lean_ctor_set(v___x_1972_, 0, v_fst_1976_);
v___x_1979_ = v___x_1972_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_fst_1976_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_x_1962_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
v_x_1961_ = v_tail_1970_;
v_x_1962_ = v___x_1979_;
v___y_1964_ = v_snd_1977_;
goto _start;
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_del_object(v___x_1972_);
lean_dec(v_tail_1970_);
lean_dec(v_x_1962_);
v_a_1982_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1974_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1974_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1961_ = stack[0].m_obj;
lean_object* v_x_1962_ = stack[1].m_obj;
lean_object* v___y_1963_ = stack[2].m_obj;
lean_object* v___y_1964_ = stack[3].m_obj;
lean_object* v_res_1991_;
v_res_1991_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1961_, v_x_1962_, v___y_1963_, v___y_1964_);
stack->m_obj
 = v_res_1991_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0___boxed(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_x_1992_, v_x_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1997_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams(lean_object* v_uparams_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_box(0);
lean_inc(v_uparams_1998_);
v___x_2003_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_1998_, v___x_2002_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_fst_2005_; lean_object* v_snd_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v_fst_2005_ = lean_ctor_get(v_a_2004_, 0);
lean_inc(v_fst_2005_);
v_snd_2006_ = lean_ctor_get(v_a_2004_, 1);
lean_inc(v_snd_2006_);
lean_dec(v_a_2004_);
v___x_2007_ = l_List_mapTR_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__1(v_uparams_1998_, v___x_2002_);
v___x_2008_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v___x_2007_, v___x_2002_, v_a_1999_, v_snd_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2026_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2026_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2026_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2024_; 
v_snd_2013_ = lean_ctor_get(v_a_2009_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_2009_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_a_2009_, 0);
lean_dec(v_unused_2025_);
v___x_2015_ = v_a_2009_;
v_isShared_2016_ = v_isSharedCheck_2024_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_dec(v_a_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2024_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2005_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2017_);
v___x_2019_ = v___x_2015_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_snd_2013_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2019_);
v___x_2021_ = v___x_2011_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_fst_2005_);
v_a_2027_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2008_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2008_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_uparams_1998_);
v_a_2035_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2003_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2003_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpUparams_0interp(lean_interpreter_value* stack)
{
lean_object* v_uparams_1998_ = stack[0].m_obj;
lean_object* v_a_1999_ = stack[1].m_obj;
lean_object* v_a_2000_ = stack[2].m_obj;
lean_object* v_res_2043_;
v_res_2043_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_1998_, v_a_1999_, v_a_2000_);
stack->m_obj
 = v_res_2043_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpUparams___boxed(lean_object* v_uparams_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_uparams_2044_, v_a_2045_, v_a_2046_);
lean_dec_ref(v_a_2045_);
return v_res_2048_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames(lean_object* v_uparams_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__0(v_uparams_2049_, v___x_2053_, v_a_2050_, v_a_2051_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2072_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2072_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2072_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_fst_2059_; lean_object* v_snd_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2071_; 
v_fst_2059_ = lean_ctor_get(v_a_2055_, 0);
v_snd_2060_ = lean_ctor_get(v_a_2055_, 1);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2062_ = v_a_2055_;
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_snd_2060_);
lean_inc(v_fst_2059_);
lean_dec(v_a_2055_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2071_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_2059_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_snd_2060_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2066_);
v___x_2068_ = v___x_2057_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2054_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2054_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_uparams_2049_ = stack[0].m_obj;
lean_object* v_a_2050_ = stack[1].m_obj;
lean_object* v_a_2051_ = stack[2].m_obj;
lean_object* v_res_2081_;
v_res_2081_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2049_, v_a_2050_, v_a_2051_);
stack->m_obj
 = v_res_2081_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpNames___boxed(lean_object* v_uparams_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_uparams_2082_, v_a_2083_, v_a_2084_);
lean_dec_ref(v_a_2083_);
return v_res_2086_;
}
}
lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(lean_object* v_msg_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___f_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___f_2104_; lean_object* v___x_11487__overap_2105_; lean_object* v___x_2106_; 
v___x_2091_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2092_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
v___f_2093_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2093_, 0, v___x_2091_);
v___f_2094_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2094_, 0, v___x_2091_);
v___f_2095_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2095_, 0, v___x_2091_);
v___x_2096_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2096_, 0, lean_box(0));
lean_closure_set(v___x_2096_, 1, lean_box(0));
lean_closure_set(v___x_2096_, 2, v___x_2091_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v___f_2092_);
v___x_2098_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2098_, 0, lean_box(0));
lean_closure_set(v___x_2098_, 1, lean_box(0));
lean_closure_set(v___x_2098_, 2, v___x_2091_);
v___x_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2097_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
lean_ctor_set(v___x_2099_, 2, v___f_2093_);
lean_ctor_set(v___x_2099_, 3, v___f_2094_);
lean_ctor_set(v___x_2099_, 4, v___f_2095_);
v___x_2100_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2100_, 0, lean_box(0));
lean_closure_set(v___x_2100_, 1, lean_box(0));
lean_closure_set(v___x_2100_, 2, v___x_2091_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_instInhabitedExpr;
v___x_2103_ = l_instInhabitedOfMonad___redArg(v___x_2101_, v___x_2102_);
v___f_2104_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2104_, 0, v___x_2103_);
v___x_11487__overap_2105_ = lean_panic_fn_borrowed(v___f_2104_, v_msg_2087_);
lean_dec_ref(v___f_2104_);
lean_inc_ref(v___y_2088_);
v___x_2106_ = lean_apply_3(v___x_11487__overap_2105_, v___y_2088_, v___y_2089_, lean_box(0));
return v___x_2106_;
}
}
LEAN_EXPORT void l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2087_ = stack[0].m_obj;
lean_object* v___y_2088_ = stack[1].m_obj;
lean_object* v___y_2089_ = stack[2].m_obj;
lean_object* v_res_2107_;
v_res_2107_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2087_, v___y_2088_, v___y_2089_);
stack->m_obj
 = v_res_2107_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2___boxed(lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v_msg_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(lean_object* v_a_2113_, lean_object* v_b_2114_, lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_dec(v_b_2114_);
lean_dec_ref(v_a_2113_);
return v_x_2115_;
}
else
{
lean_object* v_key_2116_; lean_object* v_value_2117_; lean_object* v_tail_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2130_; 
v_key_2116_ = lean_ctor_get(v_x_2115_, 0);
v_value_2117_ = lean_ctor_get(v_x_2115_, 1);
v_tail_2118_ = lean_ctor_get(v_x_2115_, 2);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_x_2115_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2120_ = v_x_2115_;
v_isShared_2121_ = v_isSharedCheck_2130_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_tail_2118_);
lean_inc(v_value_2117_);
lean_inc(v_key_2116_);
lean_dec(v_x_2115_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2130_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_expr_eqv(v_key_2116_, v_a_2113_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2113_, v_b_2114_, v_tail_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 2, v___x_2123_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_key_2116_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_value_2117_);
lean_ctor_set(v_reuseFailAlloc_2126_, 2, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_object* v___x_2128_; 
lean_dec(v_value_2117_);
lean_dec(v_key_2116_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v_b_2114_);
lean_ctor_set(v___x_2120_, 0, v_a_2113_);
v___x_2128_ = v___x_2120_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_b_2114_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_tail_2118_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
if (lean_obj_tag(v_x_2132_) == 0)
{
return v_x_2131_;
}
else
{
lean_object* v_key_2133_; lean_object* v_value_2134_; lean_object* v_tail_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2158_; 
v_key_2133_ = lean_ctor_get(v_x_2132_, 0);
v_value_2134_ = lean_ctor_get(v_x_2132_, 1);
v_tail_2135_ = lean_ctor_get(v_x_2132_, 2);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_x_2132_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2137_ = v_x_2132_;
v_isShared_2138_ = v_isSharedCheck_2158_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_tail_2135_);
lean_inc(v_value_2134_);
lean_inc(v_key_2133_);
lean_dec(v_x_2132_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2158_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; uint64_t v___x_2140_; uint64_t v___x_2141_; uint64_t v___x_2142_; uint64_t v_fold_2143_; uint64_t v___x_2144_; uint64_t v___x_2145_; uint64_t v___x_2146_; size_t v___x_2147_; size_t v___x_2148_; size_t v___x_2149_; size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2139_ = lean_array_get_size(v_x_2131_);
v___x_2140_ = l_Lean_Expr_hash(v_key_2133_);
v___x_2141_ = 32ULL;
v___x_2142_ = lean_uint64_shift_right(v___x_2140_, v___x_2141_);
v_fold_2143_ = lean_uint64_xor(v___x_2140_, v___x_2142_);
v___x_2144_ = 16ULL;
v___x_2145_ = lean_uint64_shift_right(v_fold_2143_, v___x_2144_);
v___x_2146_ = lean_uint64_xor(v_fold_2143_, v___x_2145_);
v___x_2147_ = lean_uint64_to_usize(v___x_2146_);
v___x_2148_ = lean_usize_of_nat(v___x_2139_);
v___x_2149_ = ((size_t)1ULL);
v___x_2150_ = lean_usize_sub(v___x_2148_, v___x_2149_);
v___x_2151_ = lean_usize_land(v___x_2147_, v___x_2150_);
v___x_2152_ = lean_array_uget_borrowed(v_x_2131_, v___x_2151_);
lean_inc(v___x_2152_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 2, v___x_2152_);
v___x_2154_ = v___x_2137_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_key_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_value_2134_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_array_uset(v_x_2131_, v___x_2151_, v___x_2154_);
v_x_2131_ = v___x_2155_;
v_x_2132_ = v_tail_2135_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2159_, lean_object* v_source_2160_, lean_object* v_target_2161_){
_start:
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = lean_array_get_size(v_source_2160_);
v___x_2163_ = lean_nat_dec_lt(v_i_2159_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_dec_ref(v_source_2160_);
lean_dec(v_i_2159_);
return v_target_2161_;
}
else
{
lean_object* v_es_2164_; lean_object* v___x_2165_; lean_object* v_source_2166_; lean_object* v_target_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_es_2164_ = lean_array_fget(v_source_2160_, v_i_2159_);
v___x_2165_ = lean_box(0);
v_source_2166_ = lean_array_fset(v_source_2160_, v_i_2159_, v___x_2165_);
v_target_2167_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_target_2161_, v_es_2164_);
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_add(v_i_2159_, v___x_2168_);
lean_dec(v_i_2159_);
v_i_2159_ = v___x_2169_;
v_source_2160_ = v_source_2166_;
v_target_2161_ = v_target_2167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(lean_object* v_data_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_nbuckets_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2172_ = lean_array_get_size(v_data_2171_);
v___x_2173_ = lean_unsigned_to_nat(2u);
v_nbuckets_2174_ = lean_nat_mul(v___x_2172_, v___x_2173_);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_mk_array(v_nbuckets_2174_, v___x_2176_);
v___x_2178_ = lean_array_propagate_mark(v_data_2171_, v___x_2177_);
v___x_2179_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v___x_2175_, v_data_2171_, v___x_2178_);
return v___x_2179_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(lean_object* v_a_2180_, lean_object* v_x_2181_){
_start:
{
if (lean_obj_tag(v_x_2181_) == 0)
{
uint8_t v___x_2182_; 
v___x_2182_ = 0;
return v___x_2182_;
}
else
{
lean_object* v_key_2183_; lean_object* v_tail_2184_; uint8_t v___x_2185_; 
v_key_2183_ = lean_ctor_get(v_x_2181_, 0);
v_tail_2184_ = lean_ctor_get(v_x_2181_, 2);
v___x_2185_ = lean_expr_eqv(v_key_2183_, v_a_2180_);
if (v___x_2185_ == 0)
{
v_x_2181_ = v_tail_2184_;
goto _start;
}
else
{
return v___x_2185_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2180_ = stack[0].m_obj;
lean_object* v_x_2181_ = stack[1].m_obj;
uint8_t v_res_2187_;
v_res_2187_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2180_, v_x_2181_);
stack->m_num = v_res_2187_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg___boxed(lean_object* v_a_2188_, lean_object* v_x_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2188_, v_x_2189_);
lean_dec(v_x_2189_);
lean_dec_ref(v_a_2188_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(lean_object* v_m_2192_, lean_object* v_a_2193_, lean_object* v_b_2194_){
_start:
{
lean_object* v_size_2195_; lean_object* v_buckets_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2239_; 
v_size_2195_ = lean_ctor_get(v_m_2192_, 0);
v_buckets_2196_ = lean_ctor_get(v_m_2192_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_m_2192_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2198_ = v_m_2192_;
v_isShared_2199_ = v_isSharedCheck_2239_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_buckets_2196_);
lean_inc(v_size_2195_);
lean_dec(v_m_2192_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2239_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; uint64_t v___x_2201_; uint64_t v___x_2202_; uint64_t v___x_2203_; uint64_t v_fold_2204_; uint64_t v___x_2205_; uint64_t v___x_2206_; uint64_t v___x_2207_; size_t v___x_2208_; size_t v___x_2209_; size_t v___x_2210_; size_t v___x_2211_; size_t v___x_2212_; lean_object* v_bkt_2213_; uint8_t v___x_2214_; 
v___x_2200_ = lean_array_get_size(v_buckets_2196_);
v___x_2201_ = l_Lean_Expr_hash(v_a_2193_);
v___x_2202_ = 32ULL;
v___x_2203_ = lean_uint64_shift_right(v___x_2201_, v___x_2202_);
v_fold_2204_ = lean_uint64_xor(v___x_2201_, v___x_2203_);
v___x_2205_ = 16ULL;
v___x_2206_ = lean_uint64_shift_right(v_fold_2204_, v___x_2205_);
v___x_2207_ = lean_uint64_xor(v_fold_2204_, v___x_2206_);
v___x_2208_ = lean_uint64_to_usize(v___x_2207_);
v___x_2209_ = lean_usize_of_nat(v___x_2200_);
v___x_2210_ = ((size_t)1ULL);
v___x_2211_ = lean_usize_sub(v___x_2209_, v___x_2210_);
v___x_2212_ = lean_usize_land(v___x_2208_, v___x_2211_);
v_bkt_2213_ = lean_array_uget_borrowed(v_buckets_2196_, v___x_2212_);
v___x_2214_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2193_, v_bkt_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; lean_object* v_size_x27_2216_; lean_object* v___x_2217_; lean_object* v_buckets_x27_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2215_ = lean_unsigned_to_nat(1u);
v_size_x27_2216_ = lean_nat_add(v_size_2195_, v___x_2215_);
lean_dec(v_size_2195_);
lean_inc(v_bkt_2213_);
v___x_2217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2193_);
lean_ctor_set(v___x_2217_, 1, v_b_2194_);
lean_ctor_set(v___x_2217_, 2, v_bkt_2213_);
v_buckets_x27_2218_ = lean_array_uset(v_buckets_2196_, v___x_2212_, v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(4u);
v___x_2220_ = lean_nat_mul(v_size_x27_2216_, v___x_2219_);
v___x_2221_ = lean_unsigned_to_nat(3u);
v___x_2222_ = lean_nat_div(v___x_2220_, v___x_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_array_get_size(v_buckets_x27_2218_);
v___x_2224_ = lean_nat_dec_le(v___x_2222_, v___x_2223_);
lean_dec(v___x_2222_);
if (v___x_2224_ == 0)
{
lean_object* v_val_2225_; lean_object* v___x_2227_; 
v_val_2225_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_buckets_x27_2218_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v_val_2225_);
lean_ctor_set(v___x_2198_, 0, v_size_x27_2216_);
v___x_2227_ = v___x_2198_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_size_x27_2216_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_val_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
else
{
lean_object* v___x_2230_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v_buckets_x27_2218_);
lean_ctor_set(v___x_2198_, 0, v_size_x27_2216_);
v___x_2230_ = v___x_2198_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_size_x27_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_buckets_x27_2218_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
else
{
lean_object* v___x_2232_; lean_object* v_buckets_x27_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_inc(v_bkt_2213_);
v___x_2232_ = lean_box(0);
v_buckets_x27_2233_ = lean_array_uset(v_buckets_2196_, v___x_2212_, v___x_2232_);
v___x_2234_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2193_, v_b_2194_, v_bkt_2213_);
v___x_2235_ = lean_array_uset(v_buckets_x27_2233_, v___x_2212_, v___x_2234_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2235_);
v___x_2237_ = v___x_2198_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_size_2195_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(lean_object* v_a_2240_, lean_object* v_x_2241_){
_start:
{
if (lean_obj_tag(v_x_2241_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v_key_2243_; lean_object* v_value_2244_; lean_object* v_tail_2245_; uint8_t v___x_2246_; 
v_key_2243_ = lean_ctor_get(v_x_2241_, 0);
v_value_2244_ = lean_ctor_get(v_x_2241_, 1);
v_tail_2245_ = lean_ctor_get(v_x_2241_, 2);
v___x_2246_ = lean_expr_eqv(v_key_2243_, v_a_2240_);
if (v___x_2246_ == 0)
{
v_x_2241_ = v_tail_2245_;
goto _start;
}
else
{
lean_object* v___x_2248_; 
lean_inc(v_value_2244_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_value_2244_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg___boxed(lean_object* v_a_2249_, lean_object* v_x_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2249_, v_x_2250_);
lean_dec(v_x_2250_);
lean_dec_ref(v_a_2249_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(lean_object* v_m_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_buckets_2254_; lean_object* v___x_2255_; uint64_t v___x_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v_fold_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; uint64_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_buckets_2254_ = lean_ctor_get(v_m_2252_, 1);
v___x_2255_ = lean_array_get_size(v_buckets_2254_);
v___x_2256_ = l_Lean_Expr_hash(v_a_2253_);
v___x_2257_ = 32ULL;
v___x_2258_ = lean_uint64_shift_right(v___x_2256_, v___x_2257_);
v_fold_2259_ = lean_uint64_xor(v___x_2256_, v___x_2258_);
v___x_2260_ = 16ULL;
v___x_2261_ = lean_uint64_shift_right(v_fold_2259_, v___x_2260_);
v___x_2262_ = lean_uint64_xor(v_fold_2259_, v___x_2261_);
v___x_2263_ = lean_uint64_to_usize(v___x_2262_);
v___x_2264_ = lean_usize_of_nat(v___x_2255_);
v___x_2265_ = ((size_t)1ULL);
v___x_2266_ = lean_usize_sub(v___x_2264_, v___x_2265_);
v___x_2267_ = lean_usize_land(v___x_2263_, v___x_2266_);
v___x_2268_ = lean_array_uget_borrowed(v_buckets_2254_, v___x_2267_);
v___x_2269_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2253_, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg___boxed(lean_object* v_m_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2270_, v_a_2271_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_m_2270_);
return v_res_2272_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2274_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__3));
v___x_2275_ = lean_unsigned_to_nat(26u);
v___x_2276_ = lean_unsigned_to_nat(152u);
v___x_2277_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__0));
v___x_2278_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2279_ = l_mkPanicMessageWithDecl(v___x_2278_, v___x_2277_, v___x_2276_, v___x_2275_, v___x_2274_);
return v___x_2279_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData(lean_object* v_e_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_e_x27_2285_; lean_object* v_visitedNames_2286_; lean_object* v_visitedLevels_2287_; lean_object* v_visitedExprs_2288_; lean_object* v_visitedConstants_2289_; lean_object* v_noMDataExprs_2290_; uint8_t v_exportMData_2291_; uint8_t v_exportUnsafe_2292_; uint8_t v_ignoreMissing_2293_; lean_object* v_recursorMap_2294_; lean_object* v_e_x27_2300_; lean_object* v___y_2301_; lean_object* v_visitedNames_2311_; lean_object* v_visitedLevels_2312_; lean_object* v_visitedExprs_2313_; lean_object* v_visitedConstants_2314_; lean_object* v_noMDataExprs_2315_; uint8_t v_exportMData_2316_; uint8_t v_exportUnsafe_2317_; uint8_t v_ignoreMissing_2318_; lean_object* v_recursorMap_2319_; lean_object* v___x_2320_; 
v_visitedNames_2311_ = lean_ctor_get(v_a_2282_, 0);
v_visitedLevels_2312_ = lean_ctor_get(v_a_2282_, 1);
v_visitedExprs_2313_ = lean_ctor_get(v_a_2282_, 2);
v_visitedConstants_2314_ = lean_ctor_get(v_a_2282_, 3);
v_noMDataExprs_2315_ = lean_ctor_get(v_a_2282_, 4);
v_exportMData_2316_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*6);
v_exportUnsafe_2317_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*6 + 1);
v_ignoreMissing_2318_ = lean_ctor_get_uint8(v_a_2282_, sizeof(void*)*6 + 2);
v_recursorMap_2319_ = lean_ctor_get(v_a_2282_, 5);
v___x_2320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_noMDataExprs_2315_, v_e_2280_);
if (lean_obj_tag(v___x_2320_) == 1)
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2329_; 
lean_dec_ref(v_e_2280_);
v_val_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_val_2321_);
lean_ctor_set(v___x_2325_, 1, v_a_2282_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_dec(v___x_2320_);
switch(lean_obj_tag(v_e_2280_))
{
case 1:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2331_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2330_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v_fst_2333_; lean_object* v_snd_2334_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v_fst_2333_ = lean_ctor_get(v_a_2332_, 0);
lean_inc(v_fst_2333_);
v_snd_2334_ = lean_ctor_get(v_a_2332_, 1);
lean_inc(v_snd_2334_);
lean_dec(v_a_2332_);
v_e_x27_2300_ = v_fst_2333_;
v___y_2301_ = v_snd_2334_;
goto v___jp_2299_;
}
else
{
lean_dec_ref_known(v_e_2280_, 1);
return v___x_2331_;
}
}
case 2:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1, &l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_removeMData___closed__1);
v___x_2336_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__2(v___x_2335_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v_fst_2338_; lean_object* v_snd_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v_fst_2338_ = lean_ctor_get(v_a_2337_, 0);
lean_inc(v_fst_2338_);
v_snd_2339_ = lean_ctor_get(v_a_2337_, 1);
lean_inc(v_snd_2339_);
lean_dec(v_a_2337_);
v_e_x27_2300_ = v_fst_2338_;
v___y_2301_ = v_snd_2339_;
goto v___jp_2299_;
}
else
{
lean_dec_ref_known(v_e_2280_, 1);
return v___x_2336_;
}
}
case 5:
{
lean_object* v_fn_2340_; lean_object* v_arg_2341_; lean_object* v___x_2342_; 
v_fn_2340_ = lean_ctor_get(v_e_2280_, 0);
v_arg_2341_ = lean_ctor_get(v_e_2280_, 1);
lean_inc_ref(v_fn_2340_);
v___x_2342_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_fn_2340_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v_fst_2344_; lean_object* v_snd_2345_; lean_object* v___x_2346_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v_fst_2344_ = lean_ctor_get(v_a_2343_, 0);
lean_inc(v_fst_2344_);
v_snd_2345_ = lean_ctor_get(v_a_2343_, 1);
lean_inc(v_snd_2345_);
lean_dec(v_a_2343_);
lean_inc_ref(v_arg_2341_);
v___x_2346_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_arg_2341_, v_a_2281_, v_snd_2345_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v_fst_2348_; lean_object* v_snd_2349_; size_t v___x_2350_; size_t v___x_2351_; uint8_t v___x_2352_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v_fst_2348_ = lean_ctor_get(v_a_2347_, 0);
lean_inc(v_fst_2348_);
v_snd_2349_ = lean_ctor_get(v_a_2347_, 1);
lean_inc(v_snd_2349_);
lean_dec(v_a_2347_);
v___x_2350_ = lean_ptr_addr(v_fn_2340_);
v___x_2351_ = lean_ptr_addr(v_fst_2344_);
v___x_2352_ = lean_usize_dec_eq(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Expr_app___override(v_fst_2344_, v_fst_2348_);
v_e_x27_2300_ = v___x_2353_;
v___y_2301_ = v_snd_2349_;
goto v___jp_2299_;
}
else
{
size_t v___x_2354_; size_t v___x_2355_; uint8_t v___x_2356_; 
v___x_2354_ = lean_ptr_addr(v_arg_2341_);
v___x_2355_ = lean_ptr_addr(v_fst_2348_);
v___x_2356_ = lean_usize_dec_eq(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_Expr_app___override(v_fst_2344_, v_fst_2348_);
v_e_x27_2300_ = v___x_2357_;
v___y_2301_ = v_snd_2349_;
goto v___jp_2299_;
}
else
{
lean_dec(v_fst_2348_);
lean_dec(v_fst_2344_);
lean_inc_ref(v_e_2280_);
v_e_x27_2300_ = v_e_2280_;
v___y_2301_ = v_snd_2349_;
goto v___jp_2299_;
}
}
}
else
{
lean_dec(v_fst_2344_);
lean_dec_ref_known(v_e_2280_, 2);
return v___x_2346_;
}
}
else
{
lean_dec_ref_known(v_e_2280_, 2);
return v___x_2342_;
}
}
case 6:
{
lean_object* v_binderName_2358_; lean_object* v_binderType_2359_; lean_object* v_body_2360_; uint8_t v_binderInfo_2361_; lean_object* v___x_2362_; 
v_binderName_2358_ = lean_ctor_get(v_e_2280_, 0);
v_binderType_2359_ = lean_ctor_get(v_e_2280_, 1);
v_body_2360_ = lean_ctor_get(v_e_2280_, 2);
v_binderInfo_2361_ = lean_ctor_get_uint8(v_e_2280_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2359_);
v___x_2362_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2359_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_fst_2364_; lean_object* v_snd_2365_; lean_object* v___x_2366_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v_fst_2364_ = lean_ctor_get(v_a_2363_, 0);
lean_inc(v_fst_2364_);
v_snd_2365_ = lean_ctor_get(v_a_2363_, 1);
lean_inc(v_snd_2365_);
lean_dec(v_a_2363_);
lean_inc_ref(v_body_2360_);
v___x_2366_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2360_, v_a_2281_, v_snd_2365_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_fst_2368_; lean_object* v_snd_2369_; size_t v___x_2370_; size_t v___x_2371_; uint8_t v___x_2372_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v_fst_2368_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_fst_2368_);
v_snd_2369_ = lean_ctor_get(v_a_2367_, 1);
lean_inc(v_snd_2369_);
lean_dec(v_a_2367_);
v___x_2370_ = lean_ptr_addr(v_binderType_2359_);
v___x_2371_ = lean_ptr_addr(v_fst_2364_);
v___x_2372_ = lean_usize_dec_eq(v___x_2370_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_inc(v_binderName_2358_);
v___x_2373_ = l_Lean_Expr_lam___override(v_binderName_2358_, v_fst_2364_, v_fst_2368_, v_binderInfo_2361_);
v_e_x27_2300_ = v___x_2373_;
v___y_2301_ = v_snd_2369_;
goto v___jp_2299_;
}
else
{
size_t v___x_2374_; size_t v___x_2375_; uint8_t v___x_2376_; 
v___x_2374_ = lean_ptr_addr(v_body_2360_);
v___x_2375_ = lean_ptr_addr(v_fst_2368_);
v___x_2376_ = lean_usize_dec_eq(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; 
lean_inc(v_binderName_2358_);
v___x_2377_ = l_Lean_Expr_lam___override(v_binderName_2358_, v_fst_2364_, v_fst_2368_, v_binderInfo_2361_);
v_e_x27_2300_ = v___x_2377_;
v___y_2301_ = v_snd_2369_;
goto v___jp_2299_;
}
else
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2361_, v_binderInfo_2361_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_inc(v_binderName_2358_);
v___x_2379_ = l_Lean_Expr_lam___override(v_binderName_2358_, v_fst_2364_, v_fst_2368_, v_binderInfo_2361_);
v_e_x27_2300_ = v___x_2379_;
v___y_2301_ = v_snd_2369_;
goto v___jp_2299_;
}
else
{
lean_dec(v_fst_2368_);
lean_dec(v_fst_2364_);
lean_inc_ref(v_e_2280_);
v_e_x27_2300_ = v_e_2280_;
v___y_2301_ = v_snd_2369_;
goto v___jp_2299_;
}
}
}
}
else
{
lean_dec(v_fst_2364_);
lean_dec_ref_known(v_e_2280_, 3);
return v___x_2366_;
}
}
else
{
lean_dec_ref_known(v_e_2280_, 3);
return v___x_2362_;
}
}
case 7:
{
lean_object* v_binderName_2380_; lean_object* v_binderType_2381_; lean_object* v_body_2382_; uint8_t v_binderInfo_2383_; lean_object* v___x_2384_; 
v_binderName_2380_ = lean_ctor_get(v_e_2280_, 0);
v_binderType_2381_ = lean_ctor_get(v_e_2280_, 1);
v_body_2382_ = lean_ctor_get(v_e_2280_, 2);
v_binderInfo_2383_ = lean_ctor_get_uint8(v_e_2280_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2381_);
v___x_2384_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_binderType_2381_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v_fst_2386_; lean_object* v_snd_2387_; lean_object* v___x_2388_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v_fst_2386_ = lean_ctor_get(v_a_2385_, 0);
lean_inc(v_fst_2386_);
v_snd_2387_ = lean_ctor_get(v_a_2385_, 1);
lean_inc(v_snd_2387_);
lean_dec(v_a_2385_);
lean_inc_ref(v_body_2382_);
v___x_2388_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2382_, v_a_2281_, v_snd_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v_fst_2390_; lean_object* v_snd_2391_; size_t v___x_2392_; size_t v___x_2393_; uint8_t v___x_2394_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v_fst_2390_ = lean_ctor_get(v_a_2389_, 0);
lean_inc(v_fst_2390_);
v_snd_2391_ = lean_ctor_get(v_a_2389_, 1);
lean_inc(v_snd_2391_);
lean_dec(v_a_2389_);
v___x_2392_ = lean_ptr_addr(v_binderType_2381_);
v___x_2393_ = lean_ptr_addr(v_fst_2386_);
v___x_2394_ = lean_usize_dec_eq(v___x_2392_, v___x_2393_);
if (v___x_2394_ == 0)
{
lean_object* v___x_2395_; 
lean_inc(v_binderName_2380_);
v___x_2395_ = l_Lean_Expr_forallE___override(v_binderName_2380_, v_fst_2386_, v_fst_2390_, v_binderInfo_2383_);
v_e_x27_2300_ = v___x_2395_;
v___y_2301_ = v_snd_2391_;
goto v___jp_2299_;
}
else
{
size_t v___x_2396_; size_t v___x_2397_; uint8_t v___x_2398_; 
v___x_2396_ = lean_ptr_addr(v_body_2382_);
v___x_2397_ = lean_ptr_addr(v_fst_2390_);
v___x_2398_ = lean_usize_dec_eq(v___x_2396_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; 
lean_inc(v_binderName_2380_);
v___x_2399_ = l_Lean_Expr_forallE___override(v_binderName_2380_, v_fst_2386_, v_fst_2390_, v_binderInfo_2383_);
v_e_x27_2300_ = v___x_2399_;
v___y_2301_ = v_snd_2391_;
goto v___jp_2299_;
}
else
{
uint8_t v___x_2400_; 
v___x_2400_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2383_, v_binderInfo_2383_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; 
lean_inc(v_binderName_2380_);
v___x_2401_ = l_Lean_Expr_forallE___override(v_binderName_2380_, v_fst_2386_, v_fst_2390_, v_binderInfo_2383_);
v_e_x27_2300_ = v___x_2401_;
v___y_2301_ = v_snd_2391_;
goto v___jp_2299_;
}
else
{
lean_dec(v_fst_2390_);
lean_dec(v_fst_2386_);
lean_inc_ref(v_e_2280_);
v_e_x27_2300_ = v_e_2280_;
v___y_2301_ = v_snd_2391_;
goto v___jp_2299_;
}
}
}
}
else
{
lean_dec(v_fst_2386_);
lean_dec_ref_known(v_e_2280_, 3);
return v___x_2388_;
}
}
else
{
lean_dec_ref_known(v_e_2280_, 3);
return v___x_2384_;
}
}
case 8:
{
lean_object* v_declName_2402_; lean_object* v_type_2403_; lean_object* v_value_2404_; lean_object* v_body_2405_; uint8_t v_nondep_2406_; lean_object* v___x_2407_; 
v_declName_2402_ = lean_ctor_get(v_e_2280_, 0);
v_type_2403_ = lean_ctor_get(v_e_2280_, 1);
v_value_2404_ = lean_ctor_get(v_e_2280_, 2);
v_body_2405_ = lean_ctor_get(v_e_2280_, 3);
v_nondep_2406_ = lean_ctor_get_uint8(v_e_2280_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2403_);
v___x_2407_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_type_2403_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2411_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v_fst_2409_ = lean_ctor_get(v_a_2408_, 0);
lean_inc(v_fst_2409_);
v_snd_2410_ = lean_ctor_get(v_a_2408_, 1);
lean_inc(v_snd_2410_);
lean_dec(v_a_2408_);
lean_inc_ref(v_value_2404_);
v___x_2411_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_value_2404_, v_a_2281_, v_snd_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2415_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_fst_2413_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_fst_2413_);
v_snd_2414_ = lean_ctor_get(v_a_2412_, 1);
lean_inc(v_snd_2414_);
lean_dec(v_a_2412_);
lean_inc_ref(v_body_2405_);
v___x_2415_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_body_2405_, v_a_2281_, v_snd_2414_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v_fst_2417_; lean_object* v_snd_2418_; uint8_t v___x_2419_; size_t v___x_2420_; size_t v___x_2421_; uint8_t v___x_2422_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_fst_2417_ = lean_ctor_get(v_a_2416_, 0);
lean_inc(v_fst_2417_);
v_snd_2418_ = lean_ctor_get(v_a_2416_, 1);
lean_inc(v_snd_2418_);
lean_dec(v_a_2416_);
v___x_2419_ = 0;
v___x_2420_ = lean_ptr_addr(v_type_2403_);
v___x_2421_ = lean_ptr_addr(v_fst_2409_);
v___x_2422_ = lean_usize_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
lean_inc(v_declName_2402_);
v___x_2423_ = l_Lean_Expr_letE___override(v_declName_2402_, v_fst_2409_, v_fst_2413_, v_fst_2417_, v___x_2419_);
v_e_x27_2300_ = v___x_2423_;
v___y_2301_ = v_snd_2418_;
goto v___jp_2299_;
}
else
{
size_t v___x_2424_; size_t v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = lean_ptr_addr(v_value_2404_);
v___x_2425_ = lean_ptr_addr(v_fst_2413_);
v___x_2426_ = lean_usize_dec_eq(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_inc(v_declName_2402_);
v___x_2427_ = l_Lean_Expr_letE___override(v_declName_2402_, v_fst_2409_, v_fst_2413_, v_fst_2417_, v___x_2419_);
v_e_x27_2300_ = v___x_2427_;
v___y_2301_ = v_snd_2418_;
goto v___jp_2299_;
}
else
{
size_t v___x_2428_; size_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = lean_ptr_addr(v_body_2405_);
v___x_2429_ = lean_ptr_addr(v_fst_2417_);
v___x_2430_ = lean_usize_dec_eq(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; 
lean_inc(v_declName_2402_);
v___x_2431_ = l_Lean_Expr_letE___override(v_declName_2402_, v_fst_2409_, v_fst_2413_, v_fst_2417_, v___x_2419_);
v_e_x27_2300_ = v___x_2431_;
v___y_2301_ = v_snd_2418_;
goto v___jp_2299_;
}
else
{
if (v_nondep_2406_ == 0)
{
lean_dec(v_fst_2417_);
lean_dec(v_fst_2413_);
lean_dec(v_fst_2409_);
lean_inc_ref(v_e_2280_);
v_e_x27_2300_ = v_e_2280_;
v___y_2301_ = v_snd_2418_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2432_; 
lean_inc(v_declName_2402_);
v___x_2432_ = l_Lean_Expr_letE___override(v_declName_2402_, v_fst_2409_, v_fst_2413_, v_fst_2417_, v___x_2419_);
v_e_x27_2300_ = v___x_2432_;
v___y_2301_ = v_snd_2418_;
goto v___jp_2299_;
}
}
}
}
}
else
{
lean_dec(v_fst_2413_);
lean_dec(v_fst_2409_);
lean_dec_ref_known(v_e_2280_, 4);
return v___x_2415_;
}
}
else
{
lean_dec(v_fst_2409_);
lean_dec_ref_known(v_e_2280_, 4);
return v___x_2411_;
}
}
else
{
lean_dec_ref_known(v_e_2280_, 4);
return v___x_2407_;
}
}
case 10:
{
lean_object* v_expr_2433_; lean_object* v___x_2434_; 
v_expr_2433_ = lean_ctor_get(v_e_2280_, 1);
lean_inc_ref(v_expr_2433_);
v___x_2434_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_expr_2433_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v_fst_2436_ = lean_ctor_get(v_a_2435_, 0);
lean_inc(v_fst_2436_);
v_snd_2437_ = lean_ctor_get(v_a_2435_, 1);
lean_inc(v_snd_2437_);
lean_dec(v_a_2435_);
v_e_x27_2300_ = v_fst_2436_;
v___y_2301_ = v_snd_2437_;
goto v___jp_2299_;
}
else
{
lean_dec_ref_known(v_e_2280_, 2);
return v___x_2434_;
}
}
case 11:
{
lean_object* v_typeName_2438_; lean_object* v_idx_2439_; lean_object* v_struct_2440_; lean_object* v___x_2441_; 
v_typeName_2438_ = lean_ctor_get(v_e_2280_, 0);
v_idx_2439_ = lean_ctor_get(v_e_2280_, 1);
v_struct_2440_ = lean_ctor_get(v_e_2280_, 2);
lean_inc_ref(v_struct_2440_);
v___x_2441_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_struct_2440_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v_fst_2443_; lean_object* v_snd_2444_; size_t v___x_2445_; size_t v___x_2446_; uint8_t v___x_2447_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v___x_2441_, 1);
v_fst_2443_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_fst_2443_);
v_snd_2444_ = lean_ctor_get(v_a_2442_, 1);
lean_inc(v_snd_2444_);
lean_dec(v_a_2442_);
v___x_2445_ = lean_ptr_addr(v_struct_2440_);
v___x_2446_ = lean_ptr_addr(v_fst_2443_);
v___x_2447_ = lean_usize_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
lean_inc(v_idx_2439_);
lean_inc(v_typeName_2438_);
v___x_2448_ = l_Lean_Expr_proj___override(v_typeName_2438_, v_idx_2439_, v_fst_2443_);
v_e_x27_2300_ = v___x_2448_;
v___y_2301_ = v_snd_2444_;
goto v___jp_2299_;
}
else
{
lean_dec(v_fst_2443_);
lean_inc_ref(v_e_2280_);
v_e_x27_2300_ = v_e_2280_;
v___y_2301_ = v_snd_2444_;
goto v___jp_2299_;
}
}
else
{
lean_dec_ref_known(v_e_2280_, 3);
return v___x_2441_;
}
}
default: 
{
lean_inc(v_recursorMap_2319_);
lean_inc_ref(v_noMDataExprs_2315_);
lean_inc_ref(v_visitedConstants_2314_);
lean_inc_ref(v_visitedExprs_2313_);
lean_inc_ref(v_visitedLevels_2312_);
lean_inc_ref(v_visitedNames_2311_);
lean_dec_ref(v_a_2282_);
lean_inc_ref(v_e_2280_);
v_e_x27_2285_ = v_e_2280_;
v_visitedNames_2286_ = v_visitedNames_2311_;
v_visitedLevels_2287_ = v_visitedLevels_2312_;
v_visitedExprs_2288_ = v_visitedExprs_2313_;
v_visitedConstants_2289_ = v_visitedConstants_2314_;
v_noMDataExprs_2290_ = v_noMDataExprs_2315_;
v_exportMData_2291_ = v_exportMData_2316_;
v_exportUnsafe_2292_ = v_exportUnsafe_2317_;
v_ignoreMissing_2293_ = v_ignoreMissing_2318_;
v_recursorMap_2294_ = v_recursorMap_2319_;
goto v___jp_2284_;
}
}
}
v___jp_2284_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_inc_ref(v_e_x27_2285_);
v___x_2295_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_noMDataExprs_2290_, v_e_2280_, v_e_x27_2285_);
v___x_2296_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_2296_, 0, v_visitedNames_2286_);
lean_ctor_set(v___x_2296_, 1, v_visitedLevels_2287_);
lean_ctor_set(v___x_2296_, 2, v_visitedExprs_2288_);
lean_ctor_set(v___x_2296_, 3, v_visitedConstants_2289_);
lean_ctor_set(v___x_2296_, 4, v___x_2295_);
lean_ctor_set(v___x_2296_, 5, v_recursorMap_2294_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*6, v_exportMData_2291_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*6 + 1, v_exportUnsafe_2292_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*6 + 2, v_ignoreMissing_2293_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v_e_x27_2285_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
v___jp_2299_:
{
lean_object* v_visitedNames_2302_; lean_object* v_visitedLevels_2303_; lean_object* v_visitedExprs_2304_; lean_object* v_visitedConstants_2305_; lean_object* v_noMDataExprs_2306_; uint8_t v_exportMData_2307_; uint8_t v_exportUnsafe_2308_; uint8_t v_ignoreMissing_2309_; lean_object* v_recursorMap_2310_; 
v_visitedNames_2302_ = lean_ctor_get(v___y_2301_, 0);
lean_inc_ref(v_visitedNames_2302_);
v_visitedLevels_2303_ = lean_ctor_get(v___y_2301_, 1);
lean_inc_ref(v_visitedLevels_2303_);
v_visitedExprs_2304_ = lean_ctor_get(v___y_2301_, 2);
lean_inc_ref(v_visitedExprs_2304_);
v_visitedConstants_2305_ = lean_ctor_get(v___y_2301_, 3);
lean_inc_ref(v_visitedConstants_2305_);
v_noMDataExprs_2306_ = lean_ctor_get(v___y_2301_, 4);
lean_inc_ref(v_noMDataExprs_2306_);
v_exportMData_2307_ = lean_ctor_get_uint8(v___y_2301_, sizeof(void*)*6);
v_exportUnsafe_2308_ = lean_ctor_get_uint8(v___y_2301_, sizeof(void*)*6 + 1);
v_ignoreMissing_2309_ = lean_ctor_get_uint8(v___y_2301_, sizeof(void*)*6 + 2);
v_recursorMap_2310_ = lean_ctor_get(v___y_2301_, 5);
lean_inc(v_recursorMap_2310_);
lean_dec_ref(v___y_2301_);
v_e_x27_2285_ = v_e_x27_2300_;
v_visitedNames_2286_ = v_visitedNames_2302_;
v_visitedLevels_2287_ = v_visitedLevels_2303_;
v_visitedExprs_2288_ = v_visitedExprs_2304_;
v_visitedConstants_2289_ = v_visitedConstants_2305_;
v_noMDataExprs_2290_ = v_noMDataExprs_2306_;
v_exportMData_2291_ = v_exportMData_2307_;
v_exportUnsafe_2292_ = v_exportUnsafe_2308_;
v_ignoreMissing_2293_ = v_ignoreMissing_2309_;
v_recursorMap_2294_ = v_recursorMap_2310_;
goto v___jp_2284_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_removeMData_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2280_ = stack[0].m_obj;
lean_object* v_a_2281_ = stack[1].m_obj;
lean_object* v_a_2282_ = stack[2].m_obj;
lean_object* v_res_2449_;
v_res_2449_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2280_, v_a_2281_, v_a_2282_);
stack->m_obj
 = v_res_2449_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_removeMData___boxed(lean_object* v_e_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_2450_, v_a_2451_, v_a_2452_);
lean_dec_ref(v_a_2451_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0(lean_object* v_00_u03b2_2455_, lean_object* v_m_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_m_2456_, v_a_2457_, v_b_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(lean_object* v_00_u03b2_2460_, lean_object* v_m_2461_, lean_object* v_a_2462_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_m_2461_, v_a_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___boxed(lean_object* v_00_u03b2_2464_, lean_object* v_m_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1(v_00_u03b2_2464_, v_m_2465_, v_a_2466_);
lean_dec_ref(v_a_2466_);
lean_dec_ref(v_m_2465_);
return v_res_2467_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_object* v_00_u03b2_2468_, lean_object* v_a_2469_, lean_object* v_x_2470_){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___redArg(v_a_2469_, v_x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2469_ = stack[1].m_obj;
lean_object* v_x_2470_ = stack[2].m_obj;
uint8_t v_res_2472_;
v_res_2472_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(lean_box(0), v_a_2469_, v_x_2470_);
stack->m_num = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_a_2474_, lean_object* v_x_2475_){
_start:
{
uint8_t v_res_2476_; lean_object* v_r_2477_; 
v_res_2476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__0(v_00_u03b2_2473_, v_a_2474_, v_x_2475_);
lean_dec(v_x_2475_);
lean_dec_ref(v_a_2474_);
v_r_2477_ = lean_box(v_res_2476_);
return v_r_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1(lean_object* v_00_u03b2_2478_, lean_object* v_data_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1___redArg(v_data_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2(lean_object* v_00_u03b2_2481_, lean_object* v_a_2482_, lean_object* v_b_2483_, lean_object* v_x_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__2___redArg(v_a_2482_, v_b_2483_, v_x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(lean_object* v_00_u03b2_2486_, lean_object* v_a_2487_, lean_object* v_x_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___redArg(v_a_2487_, v_x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4___boxed(lean_object* v_00_u03b2_2490_, lean_object* v_a_2491_, lean_object* v_x_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1_spec__4(v_00_u03b2_2490_, v_a_2491_, v_x_2492_);
lean_dec(v_x_2492_);
lean_dec_ref(v_a_2491_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_2494_, lean_object* v_i_2495_, lean_object* v_source_2496_, lean_object* v_target_2497_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3___redArg(v_i_2495_, v_source_2496_, v_target_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b2_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0_spec__1_spec__3_spec__5___redArg(v_x_2500_, v_x_2501_);
return v___x_2502_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(lean_object* v_fields_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = l_Lean_Json_mkObj(v_fields_2503_);
v___x_2507_ = l_Lean_Json_compress(v___x_2506_);
v___x_2508_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2517_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2517_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2509_);
lean_ctor_set(v___x_2513_, 1, v_a_2504_);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2513_);
v___x_2515_ = v___x_2511_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v_a_2504_);
v_a_2518_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2508_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2508_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fields_2503_ = stack[0].m_obj;
lean_object* v_a_2504_ = stack[1].m_obj;
lean_object* v_res_2526_;
v_res_2526_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2503_, v_a_2504_);
stack->m_obj
 = v_res_2526_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg___boxed(lean_object* v_fields_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2527_, v_a_2528_);
lean_dec(v_fields_2527_);
return v_res_2530_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(lean_object* v_fields_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v_fields_2531_, v_a_2533_);
return v___x_2535_;
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj_0interp(lean_interpreter_value* stack)
{
lean_object* v_fields_2531_ = stack[0].m_obj;
lean_object* v_a_2532_ = stack[1].m_obj;
lean_object* v_a_2533_ = stack[2].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2531_, v_a_2532_, v_a_2533_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___boxed(lean_object* v_fields_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj(v_fields_2537_, v_a_2538_, v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_fields_2537_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(lean_object* v_t_2542_, lean_object* v_k_2543_){
_start:
{
if (lean_obj_tag(v_t_2542_) == 0)
{
lean_object* v_k_2544_; lean_object* v_v_2545_; lean_object* v_l_2546_; lean_object* v_r_2547_; uint8_t v___x_2548_; 
v_k_2544_ = lean_ctor_get(v_t_2542_, 1);
v_v_2545_ = lean_ctor_get(v_t_2542_, 2);
v_l_2546_ = lean_ctor_get(v_t_2542_, 3);
v_r_2547_ = lean_ctor_get(v_t_2542_, 4);
v___x_2548_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2543_, v_k_2544_);
switch(v___x_2548_)
{
case 0:
{
v_t_2542_ = v_l_2546_;
goto _start;
}
case 1:
{
lean_object* v___x_2550_; 
lean_inc(v_v_2545_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v_v_2545_);
return v___x_2550_;
}
default: 
{
v_t_2542_ = v_r_2547_;
goto _start;
}
}
}
else
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_box(0);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg___boxed(lean_object* v_t_2553_, lean_object* v_k_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_2553_, v_k_2554_);
lean_dec(v_k_2554_);
lean_dec(v_t_2553_);
return v_res_2555_;
}
}
static lean_object* _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0(void){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Array_instInhabited___redArg();
return v___x_2556_;
}
}
lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8(lean_object* v_msg_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___x_163477__overap_2576_; lean_object* v___x_2577_; 
v___x_2561_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2562_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2562_, 0, v___x_2561_);
v___f_2563_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2563_, 0, v___x_2561_);
v___f_2564_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2564_, 0, v___x_2561_);
v___f_2565_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2565_, 0, v___x_2561_);
v___x_2566_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2566_, 0, lean_box(0));
lean_closure_set(v___x_2566_, 1, lean_box(0));
lean_closure_set(v___x_2566_, 2, v___x_2561_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___f_2562_);
v___x_2568_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2568_, 0, lean_box(0));
lean_closure_set(v___x_2568_, 1, lean_box(0));
lean_closure_set(v___x_2568_, 2, v___x_2561_);
v___x_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
lean_ctor_set(v___x_2569_, 2, v___f_2563_);
lean_ctor_set(v___x_2569_, 3, v___f_2564_);
lean_ctor_set(v___x_2569_, 4, v___f_2565_);
v___x_2570_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2570_, 0, lean_box(0));
lean_closure_set(v___x_2570_, 1, lean_box(0));
lean_closure_set(v___x_2570_, 2, v___x_2561_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
v___x_2574_ = l_instInhabitedOfMonad___redArg(v___x_2571_, v___x_2573_);
v___f_2575_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2575_, 0, v___x_2574_);
v___x_163477__overap_2576_ = lean_panic_fn_borrowed(v___f_2575_, v_msg_2557_);
lean_dec_ref(v___f_2575_);
lean_inc_ref(v___y_2558_);
v___x_2577_ = lean_apply_3(v___x_163477__overap_2576_, v___y_2558_, v___y_2559_, lean_box(0));
return v___x_2577_;
}
}
LEAN_EXPORT void l_panic___at___00LeanExport_dumpConstant_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2557_ = stack[0].m_obj;
lean_object* v___y_2558_ = stack[1].m_obj;
lean_object* v___y_2559_ = stack[2].m_obj;
lean_object* v_res_2578_;
v_res_2578_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2557_, v___y_2558_, v___y_2559_);
stack->m_obj
 = v_res_2578_;
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__8___boxed(lean_object* v_msg_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v_msg_2579_, v___y_2580_, v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2583_;
}
}
lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5(lean_object* v_msg_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___f_2601_; lean_object* v___x_162755__overap_2602_; lean_object* v___x_2603_; 
v___x_2588_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2589_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2589_, 0, v___x_2588_);
v___f_2590_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2590_, 0, v___x_2588_);
v___f_2591_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2591_, 0, v___x_2588_);
v___f_2592_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2592_, 0, v___x_2588_);
v___x_2593_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2593_, 0, lean_box(0));
lean_closure_set(v___x_2593_, 1, lean_box(0));
lean_closure_set(v___x_2593_, 2, v___x_2588_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___f_2589_);
v___x_2595_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2595_, 0, lean_box(0));
lean_closure_set(v___x_2595_, 1, lean_box(0));
lean_closure_set(v___x_2595_, 2, v___x_2588_);
v___x_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2594_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_ctor_set(v___x_2596_, 2, v___f_2590_);
lean_ctor_set(v___x_2596_, 3, v___f_2591_);
lean_ctor_set(v___x_2596_, 4, v___f_2592_);
v___x_2597_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2597_, 0, lean_box(0));
lean_closure_set(v___x_2597_, 1, lean_box(0));
lean_closure_set(v___x_2597_, 2, v___x_2588_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2596_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_box(0);
v___x_2600_ = l_instInhabitedOfMonad___redArg(v___x_2598_, v___x_2599_);
v___f_2601_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2601_, 0, v___x_2600_);
v___x_162755__overap_2602_ = lean_panic_fn_borrowed(v___f_2601_, v_msg_2584_);
lean_dec_ref(v___f_2601_);
lean_inc_ref(v___y_2585_);
v___x_2603_ = lean_apply_3(v___x_162755__overap_2602_, v___y_2585_, v___y_2586_, lean_box(0));
return v___x_2603_;
}
}
LEAN_EXPORT void l_panic___at___00LeanExport_dumpConstant_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2584_ = stack[0].m_obj;
lean_object* v___y_2585_ = stack[1].m_obj;
lean_object* v___y_2586_ = stack[2].m_obj;
lean_object* v_res_2604_;
v_res_2604_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2584_, v___y_2585_, v___y_2586_);
stack->m_obj
 = v_res_2604_;
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__5___boxed(lean_object* v_msg_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v_msg_2605_, v___y_2606_, v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__6(lean_object* v_msg_2610_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = l_Lean_instInhabitedConstantInfo_default;
v___x_2612_ = lean_panic_fn_borrowed(v___x_2611_, v_msg_2610_);
return v___x_2612_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__1));
v___x_2616_ = lean_unsigned_to_nat(10u);
v___x_2617_ = lean_unsigned_to_nat(334u);
v___x_2618_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2619_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2620_ = l_mkPanicMessageWithDecl(v___x_2619_, v___x_2618_, v___x_2617_, v___x_2616_, v___x_2615_);
return v___x_2620_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2622_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__3));
v___x_2623_ = lean_unsigned_to_nat(15u);
v___x_2624_ = lean_unsigned_to_nat(336u);
v___x_2625_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2626_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2627_ = l_mkPanicMessageWithDecl(v___x_2626_, v___x_2625_, v___x_2624_, v___x_2623_, v___x_2622_);
return v___x_2627_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__7));
v___x_2632_ = lean_unsigned_to_nat(14u);
v___x_2633_ = lean_unsigned_to_nat(22u);
v___x_2634_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__6));
v___x_2635_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__5));
v___x_2636_ = l_mkPanicMessageWithDecl(v___x_2635_, v___x_2634_, v___x_2633_, v___x_2632_, v___x_2631_);
return v___x_2636_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(uint8_t v___y_2637_, uint8_t v___x_2638_, lean_object* v_as_x27_2639_, lean_object* v_b_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
if (lean_obj_tag(v_as_x27_2639_) == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_b_2640_);
lean_ctor_set(v___x_2644_, 1, v___y_2642_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
return v___x_2645_;
}
else
{
lean_object* v_head_2646_; lean_object* v_tail_2647_; lean_object* v___y_2649_; lean_object* v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2689_; lean_object* v___x_2705_; 
v_head_2646_ = lean_ctor_get(v_as_x27_2639_, 0);
v_tail_2647_ = lean_ctor_get(v_as_x27_2639_, 1);
lean_inc(v_head_2646_);
lean_inc_ref(v___y_2641_);
v___x_2705_ = l_Lean_Environment_find_x3f(v___y_2641_, v_head_2646_, v___x_2638_);
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2707_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2706_);
v___y_2689_ = v___x_2707_;
goto v___jp_2688_;
}
else
{
lean_object* v_val_2708_; 
v_val_2708_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v___x_2705_, 1);
v___y_2689_ = v_val_2708_;
goto v___jp_2688_;
}
v___jp_2648_:
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_array_push(v_b_2640_, v___y_2649_);
v_as_x27_2639_ = v_tail_2647_;
v_b_2640_ = v___x_2650_;
goto _start;
}
v___jp_2652_:
{
if (v___y_2654_ == 0)
{
uint8_t v_exportUnsafe_2655_; 
v_exportUnsafe_2655_ = lean_ctor_get_uint8(v___y_2642_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_b_2640_);
v___x_2656_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__2);
v___x_2657_ = l_panic___at___00LeanExport_dumpConstant_spec__8(v___x_2656_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2679_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_fst_2662_; 
v_fst_2662_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_fst_2662_);
if (lean_obj_tag(v_fst_2662_) == 0)
{
lean_object* v_snd_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2674_; 
v_snd_2663_ = lean_ctor_get(v_a_2658_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_a_2658_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v_a_2658_, 0);
lean_dec(v_unused_2675_);
v___x_2665_ = v_a_2658_;
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_snd_2663_);
lean_dec(v_a_2658_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2674_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_a_2667_; lean_object* v___x_2669_; 
v_a_2667_ = lean_ctor_get(v_fst_2662_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v_fst_2662_, 1);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v_a_2667_);
v___x_2669_ = v___x_2665_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_snd_2663_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2669_);
v___x_2671_ = v___x_2660_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_snd_2676_; lean_object* v_a_2677_; 
lean_del_object(v___x_2660_);
v_snd_2676_ = lean_ctor_get(v_a_2658_, 1);
lean_inc(v_snd_2676_);
lean_dec(v_a_2658_);
v_a_2677_ = lean_ctor_get(v_fst_2662_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v_fst_2662_, 1);
v_as_x27_2639_ = v_tail_2647_;
v_b_2640_ = v_a_2677_;
v___y_2642_ = v_snd_2676_;
goto _start;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
v_a_2680_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2657_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2657_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
v___y_2649_ = v___y_2653_;
goto v___jp_2648_;
}
}
else
{
v___y_2649_ = v___y_2653_;
goto v___jp_2648_;
}
}
v___jp_2688_:
{
if (lean_obj_tag(v___y_2689_) == 6)
{
lean_object* v_val_2690_; uint8_t v_isUnsafe_2691_; 
v_val_2690_ = lean_ctor_get(v___y_2689_, 0);
lean_inc_ref(v_val_2690_);
lean_dec_ref_known(v___y_2689_, 1);
v_isUnsafe_2691_ = lean_ctor_get_uint8(v_val_2690_, sizeof(void*)*5);
if (v_isUnsafe_2691_ == 0)
{
v___y_2653_ = v_val_2690_;
v___y_2654_ = v___y_2637_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v_val_2690_;
v___y_2654_ = v___x_2638_;
goto v___jp_2652_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref(v___y_2689_);
v___x_2692_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__4);
v___x_2693_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2692_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v_snd_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v_snd_2695_ = lean_ctor_get(v_a_2694_, 1);
lean_inc(v_snd_2695_);
lean_dec(v_a_2694_);
v_as_x27_2639_ = v_tail_2647_;
v___y_2642_ = v_snd_2695_;
goto _start;
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_b_2640_);
v_a_2697_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2693_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2693_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_2637_ = stack[0].m_num;
uint8_t v___x_2638_ = stack[1].m_num;
lean_object* v_as_x27_2639_ = stack[2].m_obj;
lean_object* v_b_2640_ = stack[3].m_obj;
lean_object* v___y_2641_ = stack[4].m_obj;
lean_object* v___y_2642_ = stack[5].m_obj;
lean_object* v_res_2709_;
v_res_2709_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_2637_, v___x_2638_, v_as_x27_2639_, v_b_2640_, v___y_2641_, v___y_2642_);
stack->m_obj
 = v_res_2709_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___boxed(lean_object* v___y_2710_, lean_object* v___x_2711_, lean_object* v_as_x27_2712_, lean_object* v_b_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
uint8_t v___y_172134__boxed_2717_; uint8_t v___x_172135__boxed_2718_; lean_object* v_res_2719_; 
v___y_172134__boxed_2717_ = lean_unbox(v___y_2710_);
v___x_172135__boxed_2718_ = lean_unbox(v___x_2711_);
v_res_2719_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_172134__boxed_2717_, v___x_172135__boxed_2718_, v_as_x27_2712_, v_b_2713_, v___y_2714_, v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v_as_x27_2712_);
return v_res_2719_;
}
}
lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11(lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___f_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___f_2741_; lean_object* v___x_164159__overap_2742_; lean_object* v___x_2743_; 
v___x_2724_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2725_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2725_, 0, v___x_2724_);
v___f_2726_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2726_, 0, v___x_2724_);
v___f_2727_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2727_, 0, v___x_2724_);
v___f_2728_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2728_, 0, v___x_2724_);
v___x_2729_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2729_, 0, lean_box(0));
lean_closure_set(v___x_2729_, 1, lean_box(0));
lean_closure_set(v___x_2729_, 2, v___x_2724_);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2729_);
lean_ctor_set(v___x_2730_, 1, v___f_2725_);
v___x_2731_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2731_, 0, lean_box(0));
lean_closure_set(v___x_2731_, 1, lean_box(0));
lean_closure_set(v___x_2731_, 2, v___x_2724_);
v___x_2732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2730_);
lean_ctor_set(v___x_2732_, 1, v___x_2731_);
lean_ctor_set(v___x_2732_, 2, v___f_2726_);
lean_ctor_set(v___x_2732_, 3, v___f_2727_);
lean_ctor_set(v___x_2732_, 4, v___f_2728_);
v___x_2733_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2733_, 0, lean_box(0));
lean_closure_set(v___x_2733_, 1, lean_box(0));
lean_closure_set(v___x_2733_, 2, v___x_2724_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2736_ = lean_box(1);
v___x_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2735_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
v___x_2740_ = l_instInhabitedOfMonad___redArg(v___x_2734_, v___x_2739_);
v___f_2741_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2741_, 0, v___x_2740_);
v___x_164159__overap_2742_ = lean_panic_fn_borrowed(v___f_2741_, v_msg_2720_);
lean_dec_ref(v___f_2741_);
lean_inc_ref(v___y_2721_);
v___x_2743_ = lean_apply_3(v___x_164159__overap_2742_, v___y_2721_, v___y_2722_, lean_box(0));
return v___x_2743_;
}
}
LEAN_EXPORT void l_panic___at___00LeanExport_dumpConstant_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2720_ = stack[0].m_obj;
lean_object* v___y_2721_ = stack[1].m_obj;
lean_object* v___y_2722_ = stack[2].m_obj;
lean_object* v_res_2744_;
v_res_2744_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2720_, v___y_2721_, v___y_2722_);
stack->m_obj
 = v_res_2744_;
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__11___boxed(lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v_msg_2745_, v___y_2746_, v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2749_;
}
}
lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4(lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; lean_object* v___f_2755_; lean_object* v___f_2756_; lean_object* v___f_2757_; lean_object* v___f_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___f_2768_; lean_object* v___x_162743__overap_2769_; lean_object* v___x_2770_; 
v___x_2754_ = lean_obj_once(&l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0, &l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0_once, _init_l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2___closed__0);
v___f_2755_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2755_, 0, v___x_2754_);
v___f_2756_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2756_, 0, v___x_2754_);
v___f_2757_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_2757_, 0, v___x_2754_);
v___f_2758_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_2758_, 0, v___x_2754_);
v___x_2759_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_2759_, 0, lean_box(0));
lean_closure_set(v___x_2759_, 1, lean_box(0));
lean_closure_set(v___x_2759_, 2, v___x_2754_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
lean_ctor_set(v___x_2760_, 1, v___f_2755_);
v___x_2761_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_2761_, 0, lean_box(0));
lean_closure_set(v___x_2761_, 1, lean_box(0));
lean_closure_set(v___x_2761_, 2, v___x_2754_);
v___x_2762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
lean_ctor_set(v___x_2762_, 2, v___f_2756_);
lean_ctor_set(v___x_2762_, 3, v___f_2757_);
lean_ctor_set(v___x_2762_, 4, v___f_2758_);
v___x_2763_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_2763_, 0, lean_box(0));
lean_closure_set(v___x_2763_, 1, lean_box(0));
lean_closure_set(v___x_2763_, 2, v___x_2754_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_obj_once(&l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0, &l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0_once, _init_l_panic___at___00LeanExport_dumpConstant_spec__8___closed__0);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
v___x_2767_ = l_instInhabitedOfMonad___redArg(v___x_2764_, v___x_2766_);
v___f_2768_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2768_, 0, v___x_2767_);
v___x_162743__overap_2769_ = lean_panic_fn_borrowed(v___f_2768_, v_msg_2750_);
lean_dec_ref(v___f_2768_);
lean_inc_ref(v___y_2751_);
v___x_2770_ = lean_apply_3(v___x_162743__overap_2769_, v___y_2751_, v___y_2752_, lean_box(0));
return v___x_2770_;
}
}
LEAN_EXPORT void l_panic___at___00LeanExport_dumpConstant_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2750_ = stack[0].m_obj;
lean_object* v___y_2751_ = stack[1].m_obj;
lean_object* v___y_2752_ = stack[2].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2750_, v___y_2751_, v___y_2752_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l_panic___at___00LeanExport_dumpConstant_spec__4___boxed(lean_object* v_msg_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v_msg_2772_, v___y_2773_, v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2776_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2778_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__0));
v___x_2779_ = lean_unsigned_to_nat(8u);
v___x_2780_ = lean_unsigned_to_nat(354u);
v___x_2781_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2782_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2783_ = l_mkPanicMessageWithDecl(v___x_2782_, v___x_2781_, v___x_2780_, v___x_2779_, v___x_2778_);
return v___x_2783_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2785_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__2));
v___x_2786_ = lean_unsigned_to_nat(13u);
v___x_2787_ = lean_unsigned_to_nat(356u);
v___x_2788_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_2789_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_2790_ = l_mkPanicMessageWithDecl(v___x_2789_, v___x_2788_, v___x_2787_, v___x_2786_, v___x_2785_);
return v___x_2790_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(uint8_t v___x_2791_, lean_object* v_init_2792_, lean_object* v_x_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_d_2798_; lean_object* v___y_2799_; 
if (lean_obj_tag(v_x_2793_) == 0)
{
lean_object* v_k_2803_; lean_object* v_l_2804_; lean_object* v_r_2805_; lean_object* v___x_2806_; 
v_k_2803_ = lean_ctor_get(v_x_2793_, 1);
lean_inc(v_k_2803_);
v_l_2804_ = lean_ctor_get(v_x_2793_, 3);
lean_inc(v_l_2804_);
v_r_2805_ = lean_ctor_get(v_x_2793_, 4);
lean_inc(v_r_2805_);
lean_dec_ref_known(v_x_2793_, 5);
v___x_2806_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_2791_, v_init_2792_, v_l_2804_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_fst_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v_fst_2808_ = lean_ctor_get(v_a_2807_, 0);
lean_inc(v_fst_2808_);
if (lean_obj_tag(v_fst_2808_) == 0)
{
lean_object* v_snd_2809_; lean_object* v_a_2810_; 
lean_dec(v_r_2805_);
lean_dec(v_k_2803_);
v_snd_2809_ = lean_ctor_get(v_a_2807_, 1);
lean_inc(v_snd_2809_);
lean_dec(v_a_2807_);
v_a_2810_ = lean_ctor_get(v_fst_2808_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v_fst_2808_, 1);
v_d_2798_ = v_a_2810_;
v___y_2799_ = v_snd_2809_;
goto v___jp_2797_;
}
else
{
lean_object* v_snd_2811_; lean_object* v_a_2812_; lean_object* v___y_2814_; lean_object* v___y_2818_; lean_object* v___x_2844_; 
v_snd_2811_ = lean_ctor_get(v_a_2807_, 1);
lean_inc(v_snd_2811_);
lean_dec(v_a_2807_);
v_a_2812_ = lean_ctor_get(v_fst_2808_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v_fst_2808_, 1);
lean_inc_ref(v___y_2794_);
v___x_2844_ = l_Lean_Environment_find_x3f(v___y_2794_, v_k_2803_, v___x_2791_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_2846_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_2845_);
v___y_2818_ = v___x_2846_;
goto v___jp_2817_;
}
else
{
lean_object* v_val_2847_; 
v_val_2847_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v___x_2844_, 1);
v___y_2818_ = v_val_2847_;
goto v___jp_2817_;
}
v___jp_2813_:
{
lean_object* v___x_2815_; 
v___x_2815_ = lean_array_push(v_a_2812_, v___y_2814_);
v_init_2792_ = v___x_2815_;
v_x_2793_ = v_r_2805_;
v___y_2795_ = v_snd_2811_;
goto _start;
}
v___jp_2817_:
{
if (lean_obj_tag(v___y_2818_) == 7)
{
lean_object* v_val_2819_; uint8_t v_isUnsafe_2820_; 
v_val_2819_ = lean_ctor_get(v___y_2818_, 0);
lean_inc_ref(v_val_2819_);
lean_dec_ref_known(v___y_2818_, 1);
v_isUnsafe_2820_ = lean_ctor_get_uint8(v_val_2819_, sizeof(void*)*7 + 1);
if (v_isUnsafe_2820_ == 0)
{
v___y_2814_ = v_val_2819_;
goto v___jp_2813_;
}
else
{
if (v___x_2791_ == 0)
{
uint8_t v_exportUnsafe_2821_; 
v_exportUnsafe_2821_ = lean_ctor_get_uint8(v_snd_2811_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_2821_ == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_dec_ref(v_val_2819_);
lean_dec(v_a_2812_);
v___x_2822_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__1);
v___x_2823_ = l_panic___at___00LeanExport_dumpConstant_spec__4(v___x_2822_, v___y_2794_, v_snd_2811_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v_fst_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v_fst_2825_ = lean_ctor_get(v_a_2824_, 0);
lean_inc(v_fst_2825_);
if (lean_obj_tag(v_fst_2825_) == 0)
{
lean_object* v_snd_2826_; lean_object* v_a_2827_; 
lean_dec(v_r_2805_);
v_snd_2826_ = lean_ctor_get(v_a_2824_, 1);
lean_inc(v_snd_2826_);
lean_dec(v_a_2824_);
v_a_2827_ = lean_ctor_get(v_fst_2825_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v_fst_2825_, 1);
v_d_2798_ = v_a_2827_;
v___y_2799_ = v_snd_2826_;
goto v___jp_2797_;
}
else
{
lean_object* v_snd_2828_; lean_object* v_a_2829_; 
v_snd_2828_ = lean_ctor_get(v_a_2824_, 1);
lean_inc(v_snd_2828_);
lean_dec(v_a_2824_);
v_a_2829_ = lean_ctor_get(v_fst_2825_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v_fst_2825_, 1);
v_init_2792_ = v_a_2829_;
v_x_2793_ = v_r_2805_;
v___y_2795_ = v_snd_2828_;
goto _start;
}
}
else
{
lean_dec(v_r_2805_);
return v___x_2823_;
}
}
else
{
v___y_2814_ = v_val_2819_;
goto v___jp_2813_;
}
}
else
{
v___y_2814_ = v_val_2819_;
goto v___jp_2813_;
}
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_dec_ref(v___y_2818_);
v___x_2831_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___closed__3);
v___x_2832_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_2831_, v___y_2794_, v_snd_2811_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v_snd_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v_snd_2834_ = lean_ctor_get(v_a_2833_, 1);
lean_inc(v_snd_2834_);
lean_dec(v_a_2833_);
v_init_2792_ = v_a_2812_;
v_x_2793_ = v_r_2805_;
v___y_2795_ = v_snd_2834_;
goto _start;
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2812_);
lean_dec(v_r_2805_);
v_a_2836_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2832_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2832_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
}
}
else
{
lean_dec(v_r_2805_);
lean_dec(v_k_2803_);
return v___x_2806_;
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_init_2792_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___y_2795_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
v___jp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_d_2798_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___y_2799_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2791_ = stack[0].m_num;
lean_object* v_init_2792_ = stack[1].m_obj;
lean_object* v_x_2793_ = stack[2].m_obj;
lean_object* v___y_2794_ = stack[3].m_obj;
lean_object* v___y_2795_ = stack[4].m_obj;
lean_object* v_res_2851_;
v_res_2851_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_2791_, v_init_2792_, v_x_2793_, v___y_2794_, v___y_2795_);
stack->m_obj
 = v_res_2851_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21___boxed(lean_object* v___x_2852_, lean_object* v_init_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v___x_172577__boxed_2858_; lean_object* v_res_2859_; 
v___x_172577__boxed_2858_ = lean_unbox(v___x_2852_);
v_res_2859_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_172577__boxed_2858_, v_init_2853_, v_x_2854_, v___y_2855_, v___y_2856_);
lean_dec_ref(v___y_2855_);
return v_res_2859_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(size_t v_sz_2860_, size_t v_i_2861_, lean_object* v_bs_2862_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
if (v___x_2863_ == 0)
{
return v_bs_2862_;
}
else
{
lean_object* v_v_2864_; lean_object* v___x_2865_; lean_object* v_bs_x27_2866_; size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; 
v_v_2864_ = lean_array_uget(v_bs_2862_, v_i_2861_);
v___x_2865_ = lean_unsigned_to_nat(0u);
v_bs_x27_2866_ = lean_array_uset(v_bs_2862_, v_i_2861_, v___x_2865_);
v___x_2867_ = ((size_t)1ULL);
v___x_2868_ = lean_usize_add(v_i_2861_, v___x_2867_);
v___x_2869_ = lean_array_uset(v_bs_x27_2866_, v_i_2861_, v_v_2864_);
v_i_2861_ = v___x_2868_;
v_bs_2862_ = v___x_2869_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2860_ = stack[0].m_num;
size_t v_i_2861_ = stack[1].m_num;
lean_object* v_bs_2862_ = stack[2].m_obj;
lean_object* v_res_2871_;
v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_2860_, v_i_2861_, v_bs_2862_);
stack->m_obj
 = v_res_2871_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23___boxed(lean_object* v_sz_2872_, lean_object* v_i_2873_, lean_object* v_bs_2874_){
_start:
{
size_t v_sz_boxed_2875_; size_t v_i_boxed_2876_; lean_object* v_res_2877_; 
v_sz_boxed_2875_ = lean_unbox_usize(v_sz_2872_);
lean_dec(v_sz_2872_);
v_i_boxed_2876_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_res_2877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_boxed_2875_, v_i_boxed_2876_, v_bs_2874_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(lean_object* v_a_2878_){
_start:
{
size_t v_sz_2879_; size_t v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v_sz_2879_ = lean_array_size(v_a_2878_);
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19_spec__23(v_sz_2879_, v___x_2880_, v_a_2878_);
v___x_2882_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_array_mk(v_a_2883_);
v___x_2885_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v___x_2884_);
return v___x_2885_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(lean_object* v_as_2886_, size_t v_sz_2887_, size_t v_i_2888_, lean_object* v_b_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_usize_dec_lt(v_i_2888_, v_sz_2887_);
if (v___x_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_b_2889_);
lean_ctor_set(v___x_2894_, 1, v___y_2891_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
else
{
lean_object* v_visitedNames_2896_; lean_object* v_visitedLevels_2897_; lean_object* v_visitedExprs_2898_; lean_object* v_visitedConstants_2899_; lean_object* v_noMDataExprs_2900_; uint8_t v_exportMData_2901_; uint8_t v_exportUnsafe_2902_; uint8_t v_ignoreMissing_2903_; lean_object* v_recursorMap_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2923_; 
v_visitedNames_2896_ = lean_ctor_get(v___y_2891_, 0);
v_visitedLevels_2897_ = lean_ctor_get(v___y_2891_, 1);
v_visitedExprs_2898_ = lean_ctor_get(v___y_2891_, 2);
v_visitedConstants_2899_ = lean_ctor_get(v___y_2891_, 3);
v_noMDataExprs_2900_ = lean_ctor_get(v___y_2891_, 4);
v_exportMData_2901_ = lean_ctor_get_uint8(v___y_2891_, sizeof(void*)*6);
v_exportUnsafe_2902_ = lean_ctor_get_uint8(v___y_2891_, sizeof(void*)*6 + 1);
v_ignoreMissing_2903_ = lean_ctor_get_uint8(v___y_2891_, sizeof(void*)*6 + 2);
v_recursorMap_2904_ = lean_ctor_get(v___y_2891_, 5);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___y_2891_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2906_ = v___y_2891_;
v_isShared_2907_ = v_isSharedCheck_2923_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_recursorMap_2904_);
lean_inc(v_noMDataExprs_2900_);
lean_inc(v_visitedConstants_2899_);
lean_inc(v_visitedExprs_2898_);
lean_inc(v_visitedLevels_2897_);
lean_inc(v_visitedNames_2896_);
lean_dec(v___y_2891_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2923_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_a_2908_; lean_object* v_toConstantVal_2909_; lean_object* v_name_2910_; lean_object* v_type_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
v_a_2908_ = lean_array_uget_borrowed(v_as_2886_, v_i_2888_);
v_toConstantVal_2909_ = lean_ctor_get(v_a_2908_, 0);
v_name_2910_ = lean_ctor_get(v_toConstantVal_2909_, 0);
v_type_2911_ = lean_ctor_get(v_toConstantVal_2909_, 2);
v___x_2912_ = lean_box(0);
lean_inc(v_name_2910_);
v___x_2913_ = l_Lean_NameHashSet_insert(v_visitedConstants_2899_, v_name_2910_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 3, v___x_2913_);
v___x_2915_ = v___x_2906_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_visitedNames_2896_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_visitedLevels_2897_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_visitedExprs_2898_);
lean_ctor_set(v_reuseFailAlloc_2922_, 3, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2922_, 4, v_noMDataExprs_2900_);
lean_ctor_set(v_reuseFailAlloc_2922_, 5, v_recursorMap_2904_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*6, v_exportMData_2901_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*6 + 1, v_exportUnsafe_2902_);
lean_ctor_set_uint8(v_reuseFailAlloc_2922_, sizeof(void*)*6 + 2, v_ignoreMissing_2903_);
v___x_2915_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; 
lean_inc_ref(v_type_2911_);
v___x_2916_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_2911_, v___y_2890_, v___x_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v_snd_2918_; size_t v___x_2919_; size_t v___x_2920_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v_snd_2918_ = lean_ctor_get(v_a_2917_, 1);
lean_inc(v_snd_2918_);
lean_dec(v_a_2917_);
v___x_2919_ = ((size_t)1ULL);
v___x_2920_ = lean_usize_add(v_i_2888_, v___x_2919_);
v_i_2888_ = v___x_2920_;
v_b_2889_ = v___x_2912_;
v___y_2891_ = v_snd_2918_;
goto _start;
}
else
{
return v___x_2916_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2886_ = stack[0].m_obj;
size_t v_sz_2887_ = stack[1].m_num;
size_t v_i_2888_ = stack[2].m_num;
lean_object* v_b_2889_ = stack[3].m_obj;
lean_object* v___y_2890_ = stack[4].m_obj;
lean_object* v___y_2891_ = stack[5].m_obj;
lean_object* v_res_2924_;
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_2886_, v_sz_2887_, v_i_2888_, v_b_2889_, v___y_2890_, v___y_2891_);
stack->m_obj
 = v_res_2924_;
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(lean_object* v_as_x27_2925_, lean_object* v_b_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
if (lean_obj_tag(v_as_x27_2925_) == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v_b_2926_);
lean_ctor_set(v___x_2930_, 1, v___y_2928_);
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2930_);
return v___x_2931_;
}
else
{
lean_object* v_head_2932_; lean_object* v_tail_2933_; lean_object* v_rhs_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_head_2932_ = lean_ctor_get(v_as_x27_2925_, 0);
v_tail_2933_ = lean_ctor_get(v_as_x27_2925_, 1);
v_rhs_2934_ = lean_ctor_get(v_head_2932_, 2);
v___x_2935_ = lean_box(0);
lean_inc_ref(v_rhs_2934_);
v___x_2936_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_rhs_2934_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v_snd_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v_snd_2938_ = lean_ctor_get(v_a_2937_, 1);
lean_inc(v_snd_2938_);
lean_dec(v_a_2937_);
v_as_x27_2925_ = v_tail_2933_;
v_b_2926_ = v___x_2935_;
v___y_2928_ = v_snd_2938_;
goto _start;
}
else
{
return v___x_2936_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2925_ = stack[0].m_obj;
lean_object* v_b_2926_ = stack[1].m_obj;
lean_object* v___y_2927_ = stack[2].m_obj;
lean_object* v___y_2928_ = stack[3].m_obj;
lean_object* v_res_2940_;
v_res_2940_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_2925_, v_b_2926_, v___y_2927_, v___y_2928_);
stack->m_obj
 = v_res_2940_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(lean_object* v_as_2941_, size_t v_sz_2942_, size_t v_i_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2943_, v_sz_2942_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v_b_2944_);
lean_ctor_set(v___x_2949_, 1, v___y_2946_);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
else
{
lean_object* v_a_2951_; lean_object* v_rules_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2951_ = lean_array_uget_borrowed(v_as_2941_, v_i_2943_);
v_rules_2952_ = lean_ctor_get(v_a_2951_, 6);
v___x_2953_ = lean_box(0);
v___x_2954_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_rules_2952_, v___x_2953_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v_snd_2956_; size_t v___x_2957_; size_t v___x_2958_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v_snd_2956_ = lean_ctor_get(v_a_2955_, 1);
lean_inc(v_snd_2956_);
lean_dec(v_a_2955_);
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_add(v_i_2943_, v___x_2957_);
v_i_2943_ = v___x_2958_;
v_b_2944_ = v___x_2953_;
v___y_2946_ = v_snd_2956_;
goto _start;
}
else
{
return v___x_2954_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2941_ = stack[0].m_obj;
size_t v_sz_2942_ = stack[1].m_num;
size_t v_i_2943_ = stack[2].m_num;
lean_object* v_b_2944_ = stack[3].m_obj;
lean_object* v___y_2945_ = stack[4].m_obj;
lean_object* v___y_2946_ = stack[5].m_obj;
lean_object* v_res_2960_;
v_res_2960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_as_2941_, v_sz_2942_, v_i_2943_, v_b_2944_, v___y_2945_, v___y_2946_);
stack->m_obj
 = v_res_2960_;
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__0(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_box(0);
v___x_2962_ = lean_unsigned_to_nat(16u);
v___x_2963_ = lean_mk_array(v___x_2962_, v___x_2961_);
return v___x_2963_;
}
}
static lean_object* _init_l_LeanExport_dumpExpr___closed__1(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__0, &l_LeanExport_dumpExpr___closed__0_once, _init_l_LeanExport_dumpExpr___closed__0);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
lean_ctor_set(v___x_2966_, 1, v___x_2964_);
return v___x_2966_;
}
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(lean_object* v_a_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_visitedConstants_2993_; lean_object* v_nat_2994_; uint8_t v___x_2995_; 
v_visitedConstants_2993_ = lean_ctor_get(v_a_2987_, 3);
v_nat_2994_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___closed__1));
v___x_2995_ = l_Lean_NameHashSet_contains(v_visitedConstants_2993_, v_nat_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_inc_ref(v_a_2986_);
v___x_2996_ = l_Lean_Environment_find_x3f(v_a_2986_, v_nat_2994_, v___x_2995_);
if (lean_obj_tag(v___x_2996_) == 0)
{
goto v___jp_2989_;
}
else
{
lean_object* v___x_2997_; 
lean_dec_ref_known(v___x_2996_, 1);
v___x_2997_ = l_LeanExport_dumpConstant(v_nat_2994_, v_a_2986_, v_a_2987_);
return v___x_2997_;
}
}
else
{
goto v___jp_2989_;
}
v___jp_2989_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v_a_2987_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2986_ = stack[0].m_obj;
lean_object* v_a_2987_ = stack[1].m_obj;
lean_object* v_res_2998_;
v_res_2998_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_2986_, v_a_2987_);
stack->m_obj
 = v_res_2998_;
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v___y_3014_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v_visitedConstants_3021_; lean_object* v_visitedConstants_3026_; lean_object* v_charOfNat_3027_; uint8_t v___x_3028_; 
v_visitedConstants_3026_ = lean_ctor_get(v_a_3011_, 3);
v_charOfNat_3027_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__5));
v___x_3028_ = l_Lean_NameHashSet_contains(v_visitedConstants_3026_, v_charOfNat_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
lean_inc_ref(v_a_3010_);
v___x_3029_ = l_Lean_Environment_find_x3f(v_a_3010_, v_charOfNat_3027_, v___x_3028_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_inc_ref(v_visitedConstants_3026_);
v___y_3019_ = v_a_3010_;
v___y_3020_ = v_a_3011_;
v_visitedConstants_3021_ = v_visitedConstants_3026_;
goto v___jp_3018_;
}
else
{
lean_object* v___x_3030_; 
lean_dec_ref_known(v___x_3029_, 1);
v___x_3030_ = l_LeanExport_dumpConstant(v_charOfNat_3027_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_snd_3032_; lean_object* v_visitedConstants_3033_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v_snd_3032_ = lean_ctor_get(v_a_3031_, 1);
lean_inc(v_snd_3032_);
lean_dec(v_a_3031_);
v_visitedConstants_3033_ = lean_ctor_get(v_snd_3032_, 3);
lean_inc_ref(v_visitedConstants_3033_);
v___y_3019_ = v_a_3010_;
v___y_3020_ = v_snd_3032_;
v_visitedConstants_3021_ = v_visitedConstants_3033_;
goto v___jp_3018_;
}
else
{
return v___x_3030_;
}
}
}
else
{
lean_inc_ref(v_visitedConstants_3026_);
v___y_3019_ = v_a_3010_;
v___y_3020_ = v_a_3011_;
v_visitedConstants_3021_ = v_visitedConstants_3026_;
goto v___jp_3018_;
}
v___jp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___y_3014_);
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
return v___x_3017_;
}
v___jp_3018_:
{
lean_object* v___x_3022_; uint8_t v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___closed__2));
v___x_3023_ = l_Lean_NameHashSet_contains(v_visitedConstants_3021_, v___x_3022_);
lean_dec_ref(v_visitedConstants_3021_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_inc_ref(v___y_3019_);
v___x_3024_ = l_Lean_Environment_find_x3f(v___y_3019_, v___x_3022_, v___x_3023_);
if (lean_obj_tag(v___x_3024_) == 0)
{
v___y_3014_ = v___y_3020_;
goto v___jp_3013_;
}
else
{
lean_object* v___x_3025_; 
lean_dec_ref_known(v___x_3024_, 1);
v___x_3025_ = l_LeanExport_dumpConstant(v___x_3022_, v___y_3019_, v___y_3020_);
return v___x_3025_;
}
}
else
{
v___y_3014_ = v___y_3020_;
goto v___jp_3013_;
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3010_ = stack[0].m_obj;
lean_object* v_a_3011_ = stack[1].m_obj;
lean_object* v_res_3034_;
v_res_3034_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_3010_, v_a_3011_);
stack->m_obj
 = v_res_3034_;
}
static lean_object* _init_l_LeanExport_dumpExprAux___closed__26(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3045_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__25));
v___x_3046_ = lean_unsigned_to_nat(29u);
v___x_3047_ = lean_unsigned_to_nat(177u);
v___x_3048_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__24));
v___x_3049_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_3050_ = l_mkPanicMessageWithDecl(v___x_3049_, v___x_3048_, v___x_3047_, v___x_3046_, v___x_3045_);
return v___x_3050_;
}
}
lean_object* l_LeanExport_dumpExprAux(lean_object* v_e_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_visitedNames_3055_; lean_object* v_visitedLevels_3056_; lean_object* v_visitedExprs_3057_; lean_object* v_visitedConstants_3058_; lean_object* v_noMDataExprs_3059_; uint8_t v_exportMData_3060_; uint8_t v_exportUnsafe_3061_; uint8_t v_ignoreMissing_3062_; lean_object* v_recursorMap_3063_; lean_object* v___x_3064_; 
v_visitedNames_3055_ = lean_ctor_get(v_a_3053_, 0);
v_visitedLevels_3056_ = lean_ctor_get(v_a_3053_, 1);
v_visitedExprs_3057_ = lean_ctor_get(v_a_3053_, 2);
v_visitedConstants_3058_ = lean_ctor_get(v_a_3053_, 3);
v_noMDataExprs_3059_ = lean_ctor_get(v_a_3053_, 4);
v_exportMData_3060_ = lean_ctor_get_uint8(v_a_3053_, sizeof(void*)*6);
v_exportUnsafe_3061_ = lean_ctor_get_uint8(v_a_3053_, sizeof(void*)*6 + 1);
v_ignoreMissing_3062_ = lean_ctor_get_uint8(v_a_3053_, sizeof(void*)*6 + 2);
v_recursorMap_3063_ = lean_ctor_get(v_a_3053_, 5);
v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__1___redArg(v_visitedExprs_3057_, v_e_3051_);
if (lean_obj_tag(v___x_3064_) == 1)
{
lean_object* v_val_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_e_3051_);
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3067_ = v___x_3064_;
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_val_3065_);
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3073_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_val_3065_);
lean_ctor_set(v___x_3069_, 1, v_a_3053_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3069_);
v___x_3071_ = v___x_3067_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3069_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
else
{
lean_object* v___x_3074_; lean_object* v_fst_3076_; lean_object* v_visitedNames_3077_; lean_object* v_visitedLevels_3078_; lean_object* v_visitedExprs_3079_; lean_object* v_visitedConstants_3080_; lean_object* v_noMDataExprs_3081_; uint8_t v_exportMData_3082_; uint8_t v_exportUnsafe_3083_; uint8_t v_ignoreMissing_3084_; lean_object* v_recursorMap_3085_; lean_object* v_fst_3112_; lean_object* v_snd_3113_; 
lean_dec(v___x_3064_);
v___x_3074_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__0));
switch(lean_obj_tag(v_e_3051_))
{
case 0:
{
lean_object* v_deBruijnIndex_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_inc(v_recursorMap_3063_);
lean_inc_ref(v_noMDataExprs_3059_);
lean_inc_ref(v_visitedConstants_3058_);
lean_inc_ref(v_visitedExprs_3057_);
lean_inc_ref(v_visitedLevels_3056_);
lean_inc_ref(v_visitedNames_3055_);
lean_dec_ref(v_a_3053_);
v_deBruijnIndex_3123_ = lean_ctor_get(v_e_3051_, 0);
v___x_3124_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__1));
lean_inc(v_deBruijnIndex_3123_);
v___x_3125_ = l_Lean_JsonNumber_fromNat(v_deBruijnIndex_3123_);
v___x_3126_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3124_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3127_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = l_Lean_Json_mkObj(v___x_3129_);
lean_dec_ref_known(v___x_3129_, 2);
v_fst_3076_ = v___x_3130_;
v_visitedNames_3077_ = v_visitedNames_3055_;
v_visitedLevels_3078_ = v_visitedLevels_3056_;
v_visitedExprs_3079_ = v_visitedExprs_3057_;
v_visitedConstants_3080_ = v_visitedConstants_3058_;
v_noMDataExprs_3081_ = v_noMDataExprs_3059_;
v_exportMData_3082_ = v_exportMData_3060_;
v_exportUnsafe_3083_ = v_exportUnsafe_3061_;
v_ignoreMissing_3084_ = v_ignoreMissing_3062_;
v_recursorMap_3085_ = v_recursorMap_3063_;
goto v___jp_3075_;
}
case 3:
{
lean_object* v_u_3131_; lean_object* v___x_3132_; 
v_u_3131_ = lean_ctor_get(v_e_3051_, 0);
lean_inc(v_u_3131_);
v___x_3132_ = l___private_LeanExport_Basic_0__LeanExport_dumpLevel(v_u_3131_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3154_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3135_ = v___x_3132_;
v_isShared_3136_ = v_isSharedCheck_3154_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3132_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3154_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v_fst_3137_; lean_object* v_snd_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3153_; 
v_fst_3137_ = lean_ctor_get(v_a_3133_, 0);
v_snd_3138_ = lean_ctor_get(v_a_3133_, 1);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_a_3133_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3140_ = v_a_3133_;
v_isShared_3141_ = v_isSharedCheck_3153_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_snd_3138_);
lean_inc(v_fst_3137_);
lean_dec(v_a_3133_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3153_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3142_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__2));
v___x_3143_ = l_Lean_JsonNumber_fromNat(v_fst_3137_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 2);
lean_ctor_set(v___x_3135_, 0, v___x_3143_);
v___x_3145_ = v___x_3135_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3147_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v___x_3145_);
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
v___x_3150_ = l_Lean_Json_mkObj(v___x_3149_);
lean_dec_ref_known(v___x_3149_, 2);
v_fst_3112_ = v___x_3150_;
v_snd_3113_ = v_snd_3138_;
goto v___jp_3111_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 1);
return v___x_3132_;
}
}
case 4:
{
lean_object* v_declName_3155_; lean_object* v_us_3156_; lean_object* v___x_3157_; 
v_declName_3155_ = lean_ctor_get(v_e_3051_, 0);
v_us_3156_ = lean_ctor_get(v_e_3051_, 1);
lean_inc(v_declName_3155_);
v___x_3157_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3155_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3205_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3205_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3205_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_fst_3162_; lean_object* v_snd_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3204_; 
v_fst_3162_ = lean_ctor_get(v_a_3158_, 0);
v_snd_3163_ = lean_ctor_get(v_a_3158_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_a_3158_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3165_ = v_a_3158_;
v_isShared_3166_ = v_isSharedCheck_3204_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_snd_3163_);
lean_inc(v_fst_3162_);
lean_dec(v_a_3158_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3204_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_box(0);
lean_inc(v_us_3156_);
v___x_3168_ = l_List_mapM_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__2(v_us_3156_, v___x_3167_, v_a_3052_, v_snd_3163_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v_fst_3170_; lean_object* v_snd_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3195_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v_fst_3170_ = lean_ctor_get(v_a_3169_, 0);
v_snd_3171_ = lean_ctor_get(v_a_3169_, 1);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_a_3169_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3173_ = v_a_3169_;
v_isShared_3174_ = v_isSharedCheck_3195_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_snd_3171_);
lean_inc(v_fst_3170_);
lean_dec(v_a_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3195_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3175_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__3));
v___x_3176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3177_ = l_Lean_JsonNumber_fromNat(v_fst_3162_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set_tag(v___x_3160_, 2);
lean_ctor_set(v___x_3160_, 0, v___x_3177_);
v___x_3179_ = v___x_3160_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 1, v___x_3179_);
lean_ctor_set(v___x_3173_, 0, v___x_3176_);
v___x_3181_ = v___x_3173_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3182_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__4));
v___x_3183_ = l_Lean_List_toJson___at___00__private_LeanExport_Basic_0__LeanExport_dumpUparams_spec__3(v_fst_3170_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v___x_3183_);
lean_ctor_set(v___x_3165_, 0, v___x_3182_);
v___x_3185_ = v___x_3165_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v___x_3167_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3181_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_Json_mkObj(v___x_3187_);
lean_dec_ref_known(v___x_3187_, 2);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3175_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3167_);
v___x_3191_ = l_Lean_Json_mkObj(v___x_3190_);
lean_dec_ref_known(v___x_3190_, 2);
v_fst_3112_ = v___x_3191_;
v_snd_3113_ = v_snd_3171_;
goto v___jp_3111_;
}
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_del_object(v___x_3165_);
lean_dec(v_fst_3162_);
lean_del_object(v___x_3160_);
lean_dec_ref_known(v_e_3051_, 2);
v_a_3196_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3168_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3168_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 2);
return v___x_3157_;
}
}
case 5:
{
lean_object* v_fn_3206_; lean_object* v_arg_3207_; lean_object* v___x_3208_; 
v_fn_3206_ = lean_ctor_get(v_e_3051_, 0);
v_arg_3207_ = lean_ctor_get(v_e_3051_, 1);
lean_inc_ref(v_fn_3206_);
v___x_3208_ = l_LeanExport_dumpExprAux(v_fn_3206_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3255_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3255_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3255_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_fst_3213_; lean_object* v_snd_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3254_; 
v_fst_3213_ = lean_ctor_get(v_a_3209_, 0);
v_snd_3214_ = lean_ctor_get(v_a_3209_, 1);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_a_3209_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3216_ = v_a_3209_;
v_isShared_3217_ = v_isSharedCheck_3254_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_snd_3214_);
lean_inc(v_fst_3213_);
lean_dec(v_a_3209_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3254_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; 
lean_inc_ref(v_arg_3207_);
v___x_3218_ = l_LeanExport_dumpExprAux(v_arg_3207_, v_a_3052_, v_snd_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3253_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3221_ = v___x_3218_;
v_isShared_3222_ = v_isSharedCheck_3253_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3253_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v_fst_3223_; lean_object* v_snd_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3252_; 
v_fst_3223_ = lean_ctor_get(v_a_3219_, 0);
v_snd_3224_ = lean_ctor_get(v_a_3219_, 1);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_a_3219_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3226_ = v_a_3219_;
v_isShared_3227_ = v_isSharedCheck_3252_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snd_3224_);
lean_inc(v_fst_3223_);
lean_dec(v_a_3219_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3252_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3228_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__5));
v___x_3229_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__6));
v___x_3230_ = l_Lean_JsonNumber_fromNat(v_fst_3213_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 2);
lean_ctor_set(v___x_3221_, 0, v___x_3230_);
v___x_3232_ = v___x_3221_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 1, v___x_3232_);
lean_ctor_set(v___x_3226_, 0, v___x_3229_);
v___x_3234_ = v___x_3226_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3235_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__7));
v___x_3236_ = l_Lean_JsonNumber_fromNat(v_fst_3223_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 2);
lean_ctor_set(v___x_3211_, 0, v___x_3236_);
v___x_3238_ = v___x_3211_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3238_);
lean_ctor_set(v___x_3216_, 0, v___x_3235_);
v___x_3240_ = v___x_3216_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3241_ = lean_box(0);
v___x_3242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3234_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_Json_mkObj(v___x_3243_);
lean_dec_ref_known(v___x_3243_, 2);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3228_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v___x_3241_);
v___x_3247_ = l_Lean_Json_mkObj(v___x_3246_);
lean_dec_ref_known(v___x_3246_, 2);
v_fst_3112_ = v___x_3247_;
v_snd_3113_ = v_snd_3224_;
goto v___jp_3111_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3216_);
lean_dec(v_fst_3213_);
lean_del_object(v___x_3211_);
lean_dec_ref_known(v_e_3051_, 2);
return v___x_3218_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 2);
return v___x_3208_;
}
}
case 6:
{
lean_object* v_binderName_3256_; lean_object* v_binderType_3257_; lean_object* v_body_3258_; uint8_t v_binderInfo_3259_; lean_object* v___x_3260_; 
v_binderName_3256_ = lean_ctor_get(v_e_3051_, 0);
v_binderType_3257_ = lean_ctor_get(v_e_3051_, 1);
v_body_3258_ = lean_ctor_get(v_e_3051_, 2);
v_binderInfo_3259_ = lean_ctor_get_uint8(v_e_3051_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3256_);
v___x_3260_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3256_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3332_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3332_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3332_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v_fst_3265_; lean_object* v_snd_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3331_; 
v_fst_3265_ = lean_ctor_get(v_a_3261_, 0);
v_snd_3266_ = lean_ctor_get(v_a_3261_, 1);
v_isSharedCheck_3331_ = !lean_is_exclusive(v_a_3261_);
if (v_isSharedCheck_3331_ == 0)
{
v___x_3268_ = v_a_3261_;
v_isShared_3269_ = v_isSharedCheck_3331_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snd_3266_);
lean_inc(v_fst_3265_);
lean_dec(v_a_3261_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3331_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; 
lean_inc_ref(v_binderType_3257_);
v___x_3270_ = l_LeanExport_dumpExprAux(v_binderType_3257_, v_a_3052_, v_snd_3266_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3330_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3330_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3330_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3329_; 
v_fst_3275_ = lean_ctor_get(v_a_3271_, 0);
v_snd_3276_ = lean_ctor_get(v_a_3271_, 1);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_a_3271_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3278_ = v_a_3271_;
v_isShared_3279_ = v_isSharedCheck_3329_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snd_3276_);
lean_inc(v_fst_3275_);
lean_dec(v_a_3271_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3329_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; 
lean_inc_ref(v_body_3258_);
v___x_3280_ = l_LeanExport_dumpExprAux(v_body_3258_, v_a_3052_, v_snd_3276_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3328_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3328_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3328_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v_fst_3285_; lean_object* v_snd_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3327_; 
v_fst_3285_ = lean_ctor_get(v_a_3281_, 0);
v_snd_3286_ = lean_ctor_get(v_a_3281_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_a_3281_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3288_ = v_a_3281_;
v_isShared_3289_ = v_isSharedCheck_3327_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_snd_3286_);
lean_inc(v_fst_3285_);
lean_dec(v_a_3281_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3327_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3290_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__8));
v___x_3291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3292_ = l_Lean_JsonNumber_fromNat(v_fst_3265_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 2);
lean_ctor_set(v___x_3283_, 0, v___x_3292_);
v___x_3294_ = v___x_3283_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 1, v___x_3294_);
lean_ctor_set(v___x_3288_, 0, v___x_3291_);
v___x_3296_ = v___x_3288_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3297_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3298_ = l_Lean_JsonNumber_fromNat(v_fst_3275_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 2);
lean_ctor_set(v___x_3273_, 0, v___x_3298_);
v___x_3300_ = v___x_3273_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3298_);
v___x_3300_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; 
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 1, v___x_3300_);
lean_ctor_set(v___x_3278_, 0, v___x_3297_);
v___x_3302_ = v___x_3278_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3303_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3304_ = l_Lean_JsonNumber_fromNat(v_fst_3285_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set_tag(v___x_3263_, 2);
lean_ctor_set(v___x_3263_, 0, v___x_3304_);
v___x_3306_ = v___x_3263_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3308_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v___x_3306_);
lean_ctor_set(v___x_3268_, 0, v___x_3303_);
v___x_3308_ = v___x_3268_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3309_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3310_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3259_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3308_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3302_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3296_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_Json_mkObj(v___x_3316_);
lean_dec_ref_known(v___x_3316_, 2);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3290_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
lean_ctor_set(v___x_3319_, 1, v___x_3312_);
v___x_3320_ = l_Lean_Json_mkObj(v___x_3319_);
lean_dec_ref_known(v___x_3319_, 2);
v_fst_3112_ = v___x_3320_;
v_snd_3113_ = v_snd_3286_;
goto v___jp_3111_;
}
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
lean_del_object(v___x_3278_);
lean_dec(v_fst_3275_);
lean_del_object(v___x_3273_);
lean_del_object(v___x_3268_);
lean_dec(v_fst_3265_);
lean_del_object(v___x_3263_);
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3280_;
}
}
}
}
else
{
lean_del_object(v___x_3268_);
lean_dec(v_fst_3265_);
lean_del_object(v___x_3263_);
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3270_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3260_;
}
}
case 7:
{
lean_object* v_binderName_3333_; lean_object* v_binderType_3334_; lean_object* v_body_3335_; uint8_t v_binderInfo_3336_; lean_object* v___x_3337_; 
v_binderName_3333_ = lean_ctor_get(v_e_3051_, 0);
v_binderType_3334_ = lean_ctor_get(v_e_3051_, 1);
v_body_3335_ = lean_ctor_get(v_e_3051_, 2);
v_binderInfo_3336_ = lean_ctor_get_uint8(v_e_3051_, sizeof(void*)*3 + 8);
lean_inc(v_binderName_3333_);
v___x_3337_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_binderName_3333_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3409_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3409_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3409_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3408_; 
v_fst_3342_ = lean_ctor_get(v_a_3338_, 0);
v_snd_3343_ = lean_ctor_get(v_a_3338_, 1);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3345_ = v_a_3338_;
v_isShared_3346_ = v_isSharedCheck_3408_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_inc(v_fst_3342_);
lean_dec(v_a_3338_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3408_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; 
lean_inc_ref(v_binderType_3334_);
v___x_3347_ = l_LeanExport_dumpExprAux(v_binderType_3334_, v_a_3052_, v_snd_3343_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3407_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3407_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3407_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_fst_3352_; lean_object* v_snd_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3406_; 
v_fst_3352_ = lean_ctor_get(v_a_3348_, 0);
v_snd_3353_ = lean_ctor_get(v_a_3348_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_a_3348_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3355_ = v_a_3348_;
v_isShared_3356_ = v_isSharedCheck_3406_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_snd_3353_);
lean_inc(v_fst_3352_);
lean_dec(v_a_3348_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3406_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; 
lean_inc_ref(v_body_3335_);
v___x_3357_ = l_LeanExport_dumpExprAux(v_body_3335_, v_a_3052_, v_snd_3353_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3405_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3405_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3405_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v_fst_3362_; lean_object* v_snd_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3404_; 
v_fst_3362_ = lean_ctor_get(v_a_3358_, 0);
v_snd_3363_ = lean_ctor_get(v_a_3358_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_a_3358_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3365_ = v_a_3358_;
v_isShared_3366_ = v_isSharedCheck_3404_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3362_);
lean_dec(v_a_3358_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3404_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3367_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__11));
v___x_3368_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3369_ = l_Lean_JsonNumber_fromNat(v_fst_3342_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 2);
lean_ctor_set(v___x_3360_, 0, v___x_3369_);
v___x_3371_ = v___x_3360_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 1, v___x_3371_);
lean_ctor_set(v___x_3365_, 0, v___x_3368_);
v___x_3373_ = v___x_3365_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3374_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3375_ = l_Lean_JsonNumber_fromNat(v_fst_3352_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 2);
lean_ctor_set(v___x_3350_, 0, v___x_3375_);
v___x_3377_ = v___x_3350_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 1, v___x_3377_);
lean_ctor_set(v___x_3355_, 0, v___x_3374_);
v___x_3379_ = v___x_3355_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3380_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3381_ = l_Lean_JsonNumber_fromNat(v_fst_3362_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 2);
lean_ctor_set(v___x_3340_, 0, v___x_3381_);
v___x_3383_ = v___x_3340_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3383_);
lean_ctor_set(v___x_3345_, 0, v___x_3380_);
v___x_3385_ = v___x_3345_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3380_);
lean_ctor_set(v_reuseFailAlloc_3398_, 1, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3386_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__10));
v___x_3387_ = l___private_LeanExport_Basic_0__Lean_BinderInfo_toJson(v_binderInfo_3336_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3386_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3385_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3379_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3373_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_Json_mkObj(v___x_3393_);
lean_dec_ref_known(v___x_3393_, 2);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3367_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3389_);
v___x_3397_ = l_Lean_Json_mkObj(v___x_3396_);
lean_dec_ref_known(v___x_3396_, 2);
v_fst_3112_ = v___x_3397_;
v_snd_3113_ = v_snd_3363_;
goto v___jp_3111_;
}
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
lean_del_object(v___x_3355_);
lean_dec(v_fst_3352_);
lean_del_object(v___x_3350_);
lean_del_object(v___x_3345_);
lean_dec(v_fst_3342_);
lean_del_object(v___x_3340_);
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3357_;
}
}
}
}
else
{
lean_del_object(v___x_3345_);
lean_dec(v_fst_3342_);
lean_del_object(v___x_3340_);
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3347_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3337_;
}
}
case 8:
{
lean_object* v_declName_3410_; lean_object* v_type_3411_; lean_object* v_value_3412_; lean_object* v_body_3413_; uint8_t v_nondep_3414_; lean_object* v___x_3415_; 
v_declName_3410_ = lean_ctor_get(v_e_3051_, 0);
v_type_3411_ = lean_ctor_get(v_e_3051_, 1);
v_value_3412_ = lean_ctor_get(v_e_3051_, 2);
v_body_3413_ = lean_ctor_get(v_e_3051_, 3);
v_nondep_3414_ = lean_ctor_get_uint8(v_e_3051_, sizeof(void*)*4 + 8);
lean_inc(v_declName_3410_);
v___x_3415_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_declName_3410_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3508_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3508_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3508_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3507_; 
v_fst_3420_ = lean_ctor_get(v_a_3416_, 0);
v_snd_3421_ = lean_ctor_get(v_a_3416_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3423_ = v_a_3416_;
v_isShared_3424_ = v_isSharedCheck_3507_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3420_);
lean_dec(v_a_3416_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3507_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; 
lean_inc_ref(v_type_3411_);
v___x_3425_ = l_LeanExport_dumpExprAux(v_type_3411_, v_a_3052_, v_snd_3421_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3506_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3506_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3506_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v_fst_3430_; lean_object* v_snd_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3505_; 
v_fst_3430_ = lean_ctor_get(v_a_3426_, 0);
v_snd_3431_ = lean_ctor_get(v_a_3426_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_a_3426_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3433_ = v_a_3426_;
v_isShared_3434_ = v_isSharedCheck_3505_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_snd_3431_);
lean_inc(v_fst_3430_);
lean_dec(v_a_3426_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3505_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; 
lean_inc_ref(v_value_3412_);
v___x_3435_ = l_LeanExport_dumpExprAux(v_value_3412_, v_a_3052_, v_snd_3431_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3504_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3504_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3504_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v_fst_3440_; lean_object* v_snd_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3503_; 
v_fst_3440_ = lean_ctor_get(v_a_3436_, 0);
v_snd_3441_ = lean_ctor_get(v_a_3436_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_a_3436_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3443_ = v_a_3436_;
v_isShared_3444_ = v_isSharedCheck_3503_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_snd_3441_);
lean_inc(v_fst_3440_);
lean_dec(v_a_3436_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3503_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; 
lean_inc_ref(v_body_3413_);
v___x_3445_ = l_LeanExport_dumpExprAux(v_body_3413_, v_a_3052_, v_snd_3441_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3502_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3448_ = v___x_3445_;
v_isShared_3449_ = v_isSharedCheck_3502_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3502_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v_fst_3450_; lean_object* v_snd_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3501_; 
v_fst_3450_ = lean_ctor_get(v_a_3446_, 0);
v_snd_3451_ = lean_ctor_get(v_a_3446_, 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3453_ = v_a_3446_;
v_isShared_3454_ = v_isSharedCheck_3501_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_snd_3451_);
lean_inc(v_fst_3450_);
lean_dec(v_a_3446_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3501_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3455_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__12));
v___x_3456_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3457_ = l_Lean_JsonNumber_fromNat(v_fst_3420_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 2);
lean_ctor_set(v___x_3448_, 0, v___x_3457_);
v___x_3459_ = v___x_3448_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 1, v___x_3459_);
lean_ctor_set(v___x_3453_, 0, v___x_3456_);
v___x_3461_ = v___x_3453_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3462_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3463_ = l_Lean_JsonNumber_fromNat(v_fst_3430_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set_tag(v___x_3438_, 2);
lean_ctor_set(v___x_3438_, 0, v___x_3463_);
v___x_3465_ = v___x_3438_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3465_);
lean_ctor_set(v___x_3443_, 0, v___x_3462_);
v___x_3467_ = v___x_3443_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_3469_ = l_Lean_JsonNumber_fromNat(v_fst_3440_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set_tag(v___x_3428_, 2);
lean_ctor_set(v___x_3428_, 0, v___x_3469_);
v___x_3471_ = v___x_3428_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3473_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 1, v___x_3471_);
lean_ctor_set(v___x_3433_, 0, v___x_3468_);
v___x_3473_ = v___x_3433_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3474_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__9));
v___x_3475_ = l_Lean_JsonNumber_fromNat(v_fst_3450_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set_tag(v___x_3418_, 2);
lean_ctor_set(v___x_3418_, 0, v___x_3475_);
v___x_3477_ = v___x_3418_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3475_);
v___x_3477_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3479_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 1, v___x_3477_);
lean_ctor_set(v___x_3423_, 0, v___x_3474_);
v___x_3479_ = v___x_3423_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3480_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__14));
v___x_3481_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3481_, 0, v_nondep_3414_);
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3479_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3473_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3467_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3461_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
v___x_3489_ = l_Lean_Json_mkObj(v___x_3488_);
lean_dec_ref_known(v___x_3488_, 2);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3455_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___x_3483_);
v___x_3492_ = l_Lean_Json_mkObj(v___x_3491_);
lean_dec_ref_known(v___x_3491_, 2);
v_fst_3112_ = v___x_3492_;
v_snd_3113_ = v_snd_3451_;
goto v___jp_3111_;
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
else
{
lean_del_object(v___x_3443_);
lean_dec(v_fst_3440_);
lean_del_object(v___x_3438_);
lean_del_object(v___x_3433_);
lean_dec(v_fst_3430_);
lean_del_object(v___x_3428_);
lean_del_object(v___x_3423_);
lean_dec(v_fst_3420_);
lean_del_object(v___x_3418_);
lean_dec_ref_known(v_e_3051_, 4);
return v___x_3445_;
}
}
}
}
else
{
lean_del_object(v___x_3433_);
lean_dec(v_fst_3430_);
lean_del_object(v___x_3428_);
lean_del_object(v___x_3423_);
lean_dec(v_fst_3420_);
lean_del_object(v___x_3418_);
lean_dec_ref_known(v_e_3051_, 4);
return v___x_3435_;
}
}
}
}
else
{
lean_del_object(v___x_3423_);
lean_dec(v_fst_3420_);
lean_del_object(v___x_3418_);
lean_dec_ref_known(v_e_3051_, 4);
return v___x_3425_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 4);
return v___x_3415_;
}
}
case 9:
{
lean_object* v_a_3509_; 
v_a_3509_ = lean_ctor_get(v_e_3051_, 0);
lean_inc_ref(v_a_3509_);
if (lean_obj_tag(v_a_3509_) == 0)
{
lean_object* v_val_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3541_; 
v_val_3510_ = lean_ctor_get(v_a_3509_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3512_ = v_a_3509_;
v_isShared_3513_ = v_isSharedCheck_3541_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_val_3510_);
lean_dec(v_a_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3541_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; 
v___x_3514_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v_snd_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3531_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v_snd_3516_ = lean_ctor_get(v_a_3515_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_a_3515_, 0);
lean_dec(v_unused_3532_);
v___x_3518_ = v_a_3515_;
v_isShared_3519_ = v_isSharedCheck_3531_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_snd_3516_);
lean_dec(v_a_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3531_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__15));
v___x_3521_ = l_Nat_reprFast(v_val_3510_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set_tag(v___x_3512_, 3);
lean_ctor_set(v___x_3512_, 0, v___x_3521_);
v___x_3523_ = v___x_3512_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v___x_3523_);
lean_ctor_set(v___x_3518_, 0, v___x_3520_);
v___x_3525_ = v___x_3518_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3526_ = lean_box(0);
v___x_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = l_Lean_Json_mkObj(v___x_3527_);
lean_dec_ref_known(v___x_3527_, 2);
v_fst_3112_ = v___x_3528_;
v_snd_3113_ = v_snd_3516_;
goto v___jp_3111_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3512_);
lean_dec(v_val_3510_);
lean_dec_ref_known(v_e_3051_, 1);
v_a_3533_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3514_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3514_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
else
{
lean_object* v_val_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3572_; 
v_val_3542_ = lean_ctor_get(v_a_3509_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3544_ = v_a_3509_;
v_isShared_3545_ = v_isSharedCheck_3572_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_val_3542_);
lean_dec(v_a_3509_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3572_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; 
v___x_3546_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v_snd_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3562_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v_snd_3548_ = lean_ctor_get(v_a_3547_, 1);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_a_3547_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v_a_3547_, 0);
lean_dec(v_unused_3563_);
v___x_3550_ = v_a_3547_;
v_isShared_3551_ = v_isSharedCheck_3562_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_snd_3548_);
lean_dec(v_a_3547_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3562_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3552_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__16));
if (v_isShared_3545_ == 0)
{
lean_ctor_set_tag(v___x_3544_, 3);
v___x_3554_ = v___x_3544_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_val_3542_);
v___x_3554_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
lean_object* v___x_3556_; 
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 1, v___x_3554_);
lean_ctor_set(v___x_3550_, 0, v___x_3552_);
v___x_3556_ = v___x_3550_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_box(0);
v___x_3558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3556_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = l_Lean_Json_mkObj(v___x_3558_);
lean_dec_ref_known(v___x_3558_, 2);
v_fst_3112_ = v___x_3559_;
v_snd_3113_ = v_snd_3548_;
goto v___jp_3111_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_del_object(v___x_3544_);
lean_dec_ref(v_val_3542_);
lean_dec_ref_known(v_e_3051_, 1);
v_a_3564_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3546_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3546_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
}
case 10:
{
lean_object* v_data_3573_; lean_object* v_expr_3574_; lean_object* v___x_3575_; 
v_data_3573_ = lean_ctor_get(v_e_3051_, 0);
v_expr_3574_ = lean_ctor_get(v_e_3051_, 1);
lean_inc_ref(v_expr_3574_);
v___x_3575_ = l_LeanExport_dumpExprAux(v_expr_3574_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3605_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3605_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3605_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_fst_3580_; lean_object* v_snd_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3604_; 
v_fst_3580_ = lean_ctor_get(v_a_3576_, 0);
v_snd_3581_ = lean_ctor_get(v_a_3576_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_a_3576_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3583_ = v_a_3576_;
v_isShared_3584_ = v_isSharedCheck_3604_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_snd_3581_);
lean_inc(v_fst_3580_);
lean_dec(v_a_3576_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3604_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3585_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__17));
v___x_3586_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__18));
lean_inc(v_data_3573_);
v___x_3587_ = l___private_LeanExport_Basic_0__Lean_KVMap_toJson(v_data_3573_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 1, v___x_3587_);
lean_ctor_set(v___x_3583_, 0, v___x_3586_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3590_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__19));
v___x_3591_ = l_Lean_JsonNumber_fromNat(v_fst_3580_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 2);
lean_ctor_set(v___x_3578_, 0, v___x_3591_);
v___x_3593_ = v___x_3578_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3590_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3594_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3589_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = l_Lean_Json_mkObj(v___x_3597_);
lean_dec_ref_known(v___x_3597_, 2);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3585_);
lean_ctor_set(v___x_3599_, 1, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3595_);
v___x_3601_ = l_Lean_Json_mkObj(v___x_3600_);
lean_dec_ref_known(v___x_3600_, 2);
v_fst_3112_ = v___x_3601_;
v_snd_3113_ = v_snd_3581_;
goto v___jp_3111_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 2);
return v___x_3575_;
}
}
case 11:
{
lean_object* v_typeName_3606_; lean_object* v_idx_3607_; lean_object* v_struct_3608_; lean_object* v___x_3609_; 
v_typeName_3606_ = lean_ctor_get(v_e_3051_, 0);
v_idx_3607_ = lean_ctor_get(v_e_3051_, 1);
v_struct_3608_ = lean_ctor_get(v_e_3051_, 2);
lean_inc(v_typeName_3606_);
v___x_3609_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_typeName_3606_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3661_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3661_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3661_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v_fst_3614_; lean_object* v_snd_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3660_; 
v_fst_3614_ = lean_ctor_get(v_a_3610_, 0);
v_snd_3615_ = lean_ctor_get(v_a_3610_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_a_3610_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3617_ = v_a_3610_;
v_isShared_3618_ = v_isSharedCheck_3660_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_snd_3615_);
lean_inc(v_fst_3614_);
lean_dec(v_a_3610_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3660_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; 
lean_inc_ref(v_struct_3608_);
v___x_3619_ = l_LeanExport_dumpExprAux(v_struct_3608_, v_a_3052_, v_snd_3615_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3659_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3659_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3659_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v_fst_3624_; lean_object* v_snd_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3658_; 
v_fst_3624_ = lean_ctor_get(v_a_3620_, 0);
v_snd_3625_ = lean_ctor_get(v_a_3620_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_a_3620_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3627_ = v_a_3620_;
v_isShared_3628_ = v_isSharedCheck_3658_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_snd_3625_);
lean_inc(v_fst_3624_);
lean_dec(v_a_3620_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3658_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3629_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__20));
v___x_3630_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__21));
v___x_3631_ = l_Lean_JsonNumber_fromNat(v_fst_3614_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set_tag(v___x_3622_, 2);
lean_ctor_set(v___x_3622_, 0, v___x_3631_);
v___x_3633_ = v___x_3622_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 1, v___x_3633_);
lean_ctor_set(v___x_3627_, 0, v___x_3630_);
v___x_3635_ = v___x_3627_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3639_; 
v___x_3636_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__22));
lean_inc(v_idx_3607_);
v___x_3637_ = l_Lean_JsonNumber_fromNat(v_idx_3607_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 2);
lean_ctor_set(v___x_3612_, 0, v___x_3637_);
v___x_3639_ = v___x_3612_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 1, v___x_3639_);
lean_ctor_set(v___x_3617_, 0, v___x_3636_);
v___x_3641_ = v___x_3617_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3642_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__23));
v___x_3643_ = l_Lean_JsonNumber_fromNat(v_fst_3624_);
v___x_3644_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3642_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_box(0);
v___x_3647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3641_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3635_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = l_Lean_Json_mkObj(v___x_3649_);
lean_dec_ref_known(v___x_3649_, 2);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3629_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v___x_3646_);
v___x_3653_ = l_Lean_Json_mkObj(v___x_3652_);
lean_dec_ref_known(v___x_3652_, 2);
v_fst_3112_ = v___x_3653_;
v_snd_3113_ = v_snd_3625_;
goto v___jp_3111_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3617_);
lean_dec(v_fst_3614_);
lean_del_object(v___x_3612_);
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3619_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3051_, 3);
return v___x_3609_;
}
}
default: 
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = lean_obj_once(&l_LeanExport_dumpExprAux___closed__26, &l_LeanExport_dumpExprAux___closed__26_once, _init_l_LeanExport_dumpExprAux___closed__26);
v___x_3663_ = l_panic___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__2(v___x_3662_, v_a_3052_, v_a_3053_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v_fst_3665_; lean_object* v_snd_3666_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v_fst_3665_ = lean_ctor_get(v_a_3664_, 0);
lean_inc(v_fst_3665_);
v_snd_3666_ = lean_ctor_get(v_a_3664_, 1);
lean_inc(v_snd_3666_);
lean_dec(v_a_3664_);
v_fst_3112_ = v_fst_3665_;
v_snd_3113_ = v_snd_3666_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec_ref(v_e_3051_);
v_a_3667_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3663_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3663_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
v___jp_3075_:
{
lean_object* v_size_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v_size_3086_ = lean_ctor_get(v_visitedExprs_3079_, 0);
lean_inc_n(v_size_3086_, 2);
v___x_3087_ = l_Lean_JsonNumber_fromNat(v_size_3086_);
v___x_3088_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = l_Lean_Json_setObjVal_x21(v_fst_3076_, v___x_3074_, v___x_3088_);
v___x_3090_ = l_Lean_Json_compress(v___x_3089_);
v___x_3091_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_3090_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3101_; 
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3091_, 0);
lean_dec(v_unused_3102_);
v___x_3093_ = v___x_3091_;
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v___x_3091_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3101_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
lean_inc(v_size_3086_);
v___x_3095_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_LeanExport_Basic_0__LeanExport_removeMData_spec__0___redArg(v_visitedExprs_3079_, v_e_3051_, v_size_3086_);
v___x_3096_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_3096_, 0, v_visitedNames_3077_);
lean_ctor_set(v___x_3096_, 1, v_visitedLevels_3078_);
lean_ctor_set(v___x_3096_, 2, v___x_3095_);
lean_ctor_set(v___x_3096_, 3, v_visitedConstants_3080_);
lean_ctor_set(v___x_3096_, 4, v_noMDataExprs_3081_);
lean_ctor_set(v___x_3096_, 5, v_recursorMap_3085_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*6, v_exportMData_3082_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*6 + 1, v_exportUnsafe_3083_);
lean_ctor_set_uint8(v___x_3096_, sizeof(void*)*6 + 2, v_ignoreMissing_3084_);
v___x_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3097_, 0, v_size_3086_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3097_);
v___x_3099_ = v___x_3093_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_size_3086_);
lean_dec(v_recursorMap_3085_);
lean_dec_ref(v_noMDataExprs_3081_);
lean_dec_ref(v_visitedConstants_3080_);
lean_dec_ref(v_visitedExprs_3079_);
lean_dec_ref(v_visitedLevels_3078_);
lean_dec_ref(v_visitedNames_3077_);
lean_dec_ref(v_e_3051_);
v_a_3103_ = lean_ctor_get(v___x_3091_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3091_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3091_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
v___jp_3111_:
{
lean_object* v_visitedNames_3114_; lean_object* v_visitedLevels_3115_; lean_object* v_visitedExprs_3116_; lean_object* v_visitedConstants_3117_; lean_object* v_noMDataExprs_3118_; uint8_t v_exportMData_3119_; uint8_t v_exportUnsafe_3120_; uint8_t v_ignoreMissing_3121_; lean_object* v_recursorMap_3122_; 
v_visitedNames_3114_ = lean_ctor_get(v_snd_3113_, 0);
lean_inc_ref(v_visitedNames_3114_);
v_visitedLevels_3115_ = lean_ctor_get(v_snd_3113_, 1);
lean_inc_ref(v_visitedLevels_3115_);
v_visitedExprs_3116_ = lean_ctor_get(v_snd_3113_, 2);
lean_inc_ref(v_visitedExprs_3116_);
v_visitedConstants_3117_ = lean_ctor_get(v_snd_3113_, 3);
lean_inc_ref(v_visitedConstants_3117_);
v_noMDataExprs_3118_ = lean_ctor_get(v_snd_3113_, 4);
lean_inc_ref(v_noMDataExprs_3118_);
v_exportMData_3119_ = lean_ctor_get_uint8(v_snd_3113_, sizeof(void*)*6);
v_exportUnsafe_3120_ = lean_ctor_get_uint8(v_snd_3113_, sizeof(void*)*6 + 1);
v_ignoreMissing_3121_ = lean_ctor_get_uint8(v_snd_3113_, sizeof(void*)*6 + 2);
v_recursorMap_3122_ = lean_ctor_get(v_snd_3113_, 5);
lean_inc(v_recursorMap_3122_);
lean_dec_ref(v_snd_3113_);
v_fst_3076_ = v_fst_3112_;
v_visitedNames_3077_ = v_visitedNames_3114_;
v_visitedLevels_3078_ = v_visitedLevels_3115_;
v_visitedExprs_3079_ = v_visitedExprs_3116_;
v_visitedConstants_3080_ = v_visitedConstants_3117_;
v_noMDataExprs_3081_ = v_noMDataExprs_3118_;
v_exportMData_3082_ = v_exportMData_3119_;
v_exportUnsafe_3083_ = v_exportUnsafe_3120_;
v_ignoreMissing_3084_ = v_ignoreMissing_3121_;
v_recursorMap_3085_ = v_recursorMap_3122_;
goto v___jp_3075_;
}
}
}
}
LEAN_EXPORT void l_LeanExport_dumpExprAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3051_ = stack[0].m_obj;
lean_object* v_a_3052_ = stack[1].m_obj;
lean_object* v_a_3053_ = stack[2].m_obj;
lean_object* v_res_3675_;
v_res_3675_ = l_LeanExport_dumpExprAux(v_e_3051_, v_a_3052_, v_a_3053_);
stack->m_obj
 = v_res_3675_;
}
lean_object* l_LeanExport_dumpExpr(lean_object* v_e_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_){
_start:
{
uint8_t v_exportMData_3680_; 
v_exportMData_3680_ = lean_ctor_get_uint8(v_a_3678_, sizeof(void*)*6);
if (v_exportMData_3680_ == 0)
{
lean_object* v_visitedNames_3681_; lean_object* v_visitedLevels_3682_; lean_object* v_visitedExprs_3683_; lean_object* v_visitedConstants_3684_; uint8_t v_exportUnsafe_3685_; uint8_t v_ignoreMissing_3686_; lean_object* v_recursorMap_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3708_; 
v_visitedNames_3681_ = lean_ctor_get(v_a_3678_, 0);
v_visitedLevels_3682_ = lean_ctor_get(v_a_3678_, 1);
v_visitedExprs_3683_ = lean_ctor_get(v_a_3678_, 2);
v_visitedConstants_3684_ = lean_ctor_get(v_a_3678_, 3);
v_exportUnsafe_3685_ = lean_ctor_get_uint8(v_a_3678_, sizeof(void*)*6 + 1);
v_ignoreMissing_3686_ = lean_ctor_get_uint8(v_a_3678_, sizeof(void*)*6 + 2);
v_recursorMap_3687_ = lean_ctor_get(v_a_3678_, 5);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3678_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_a_3678_, 4);
lean_dec(v_unused_3709_);
v___x_3689_ = v_a_3678_;
v_isShared_3690_ = v_isSharedCheck_3708_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_recursorMap_3687_);
lean_inc(v_visitedConstants_3684_);
lean_inc(v_visitedExprs_3683_);
lean_inc(v_visitedLevels_3682_);
lean_inc(v_visitedNames_3681_);
lean_dec(v_a_3678_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3708_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 4, v___x_3691_);
v___x_3693_ = v___x_3689_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_visitedNames_3681_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_visitedLevels_3682_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_visitedExprs_3683_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v_visitedConstants_3684_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3707_, 5, v_recursorMap_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3707_, sizeof(void*)*6, v_exportMData_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3707_, sizeof(void*)*6 + 1, v_exportUnsafe_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3707_, sizeof(void*)*6 + 2, v_ignoreMissing_3686_);
v___x_3693_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; 
v___x_3694_ = l___private_LeanExport_Basic_0__LeanExport_removeMData(v_e_3676_, v_a_3677_, v___x_3693_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v_fst_3696_; lean_object* v_snd_3697_; lean_object* v___x_3698_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
lean_inc(v_a_3695_);
lean_dec_ref_known(v___x_3694_, 1);
v_fst_3696_ = lean_ctor_get(v_a_3695_, 0);
lean_inc(v_fst_3696_);
v_snd_3697_ = lean_ctor_get(v_a_3695_, 1);
lean_inc(v_snd_3697_);
lean_dec(v_a_3695_);
v___x_3698_ = l_LeanExport_dumpExprAux(v_fst_3696_, v_a_3677_, v_snd_3697_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_a_3699_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3694_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3694_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
}
}
else
{
lean_object* v___x_3710_; 
v___x_3710_ = l_LeanExport_dumpExprAux(v_e_3676_, v_a_3677_, v_a_3678_);
return v___x_3710_;
}
}
}
LEAN_EXPORT void l_LeanExport_dumpExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3676_ = stack[0].m_obj;
lean_object* v_a_3677_ = stack[1].m_obj;
lean_object* v_a_3678_ = stack[2].m_obj;
lean_object* v_res_3711_;
v_res_3711_ = l_LeanExport_dumpExpr(v_e_3676_, v_a_3677_, v_a_3678_);
stack->m_obj
 = v_res_3711_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_bs_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v___x_3727_; 
v___x_3727_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_bs_3723_);
lean_ctor_set(v___x_3728_, 1, v___y_3725_);
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
return v___x_3729_;
}
else
{
lean_object* v_v_3730_; lean_object* v_toConstantVal_3731_; lean_object* v_numParams_3732_; lean_object* v_numIndices_3733_; lean_object* v_all_3734_; lean_object* v_ctors_3735_; lean_object* v_numNested_3736_; uint8_t v_isRec_3737_; uint8_t v_isUnsafe_3738_; uint8_t v_isReflexive_3739_; lean_object* v_name_3740_; lean_object* v_levelParams_3741_; lean_object* v_type_3742_; lean_object* v___x_3743_; lean_object* v_bs_x27_3744_; lean_object* v_fst_3746_; lean_object* v_snd_3747_; lean_object* v___y_3753_; lean_object* v___x_3765_; 
v_v_3730_ = lean_array_uget_borrowed(v_bs_3723_, v_i_3722_);
v_toConstantVal_3731_ = lean_ctor_get(v_v_3730_, 0);
v_numParams_3732_ = lean_ctor_get(v_v_3730_, 1);
lean_inc(v_numParams_3732_);
v_numIndices_3733_ = lean_ctor_get(v_v_3730_, 2);
lean_inc(v_numIndices_3733_);
v_all_3734_ = lean_ctor_get(v_v_3730_, 3);
lean_inc(v_all_3734_);
v_ctors_3735_ = lean_ctor_get(v_v_3730_, 4);
lean_inc(v_ctors_3735_);
v_numNested_3736_ = lean_ctor_get(v_v_3730_, 5);
lean_inc(v_numNested_3736_);
v_isRec_3737_ = lean_ctor_get_uint8(v_v_3730_, sizeof(void*)*6);
v_isUnsafe_3738_ = lean_ctor_get_uint8(v_v_3730_, sizeof(void*)*6 + 1);
v_isReflexive_3739_ = lean_ctor_get_uint8(v_v_3730_, sizeof(void*)*6 + 2);
v_name_3740_ = lean_ctor_get(v_toConstantVal_3731_, 0);
lean_inc(v_name_3740_);
v_levelParams_3741_ = lean_ctor_get(v_toConstantVal_3731_, 1);
lean_inc(v_levelParams_3741_);
v_type_3742_ = lean_ctor_get(v_toConstantVal_3731_, 2);
lean_inc_ref(v_type_3742_);
v___x_3743_ = lean_unsigned_to_nat(0u);
v_bs_x27_3744_ = lean_array_uset(v_bs_3723_, v_i_3722_, v___x_3743_);
v___x_3765_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3740_, v___y_3724_, v___y_3725_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v_fst_3767_; lean_object* v_snd_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3888_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3765_, 1);
v_fst_3767_ = lean_ctor_get(v_a_3766_, 0);
v_snd_3768_ = lean_ctor_get(v_a_3766_, 1);
v_isSharedCheck_3888_ = !lean_is_exclusive(v_a_3766_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3770_ = v_a_3766_;
v_isShared_3771_ = v_isSharedCheck_3888_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_snd_3768_);
lean_inc(v_fst_3767_);
lean_dec(v_a_3766_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3888_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3741_, v___y_3724_, v_snd_3768_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3887_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3775_ = v___x_3772_;
v_isShared_3776_ = v_isSharedCheck_3887_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3772_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3887_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v_fst_3777_; lean_object* v_snd_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3886_; 
v_fst_3777_ = lean_ctor_get(v_a_3773_, 0);
v_snd_3778_ = lean_ctor_get(v_a_3773_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v_a_3773_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3780_ = v_a_3773_;
v_isShared_3781_ = v_isSharedCheck_3886_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_snd_3778_);
lean_inc(v_fst_3777_);
lean_dec(v_a_3773_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3886_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_LeanExport_dumpExpr(v_type_3742_, v___y_3724_, v_snd_3778_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v_fst_3784_; lean_object* v_snd_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3877_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v_fst_3784_ = lean_ctor_get(v_a_3783_, 0);
v_snd_3785_ = lean_ctor_get(v_a_3783_, 1);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_a_3783_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3787_ = v_a_3783_;
v_isShared_3788_ = v_isSharedCheck_3877_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_snd_3785_);
lean_inc(v_fst_3784_);
lean_dec(v_a_3783_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3877_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; 
v___x_3789_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_3734_, v___y_3724_, v_snd_3785_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3876_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3876_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3876_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_fst_3794_; lean_object* v_snd_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3875_; 
v_fst_3794_ = lean_ctor_get(v_a_3790_, 0);
v_snd_3795_ = lean_ctor_get(v_a_3790_, 1);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_a_3790_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3797_ = v_a_3790_;
v_isShared_3798_ = v_isSharedCheck_3875_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_snd_3795_);
lean_inc(v_fst_3794_);
lean_dec(v_a_3790_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3875_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3799_; 
v___x_3799_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_ctors_3735_, v___y_3724_, v_snd_3795_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3874_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3874_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3874_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_fst_3804_; lean_object* v_snd_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3873_; 
v_fst_3804_ = lean_ctor_get(v_a_3800_, 0);
v_snd_3805_ = lean_ctor_get(v_a_3800_, 1);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_a_3800_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3807_ = v_a_3800_;
v_isShared_3808_ = v_isSharedCheck_3873_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_snd_3805_);
lean_inc(v_fst_3804_);
lean_dec(v_a_3800_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3873_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3809_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3810_ = l_Lean_JsonNumber_fromNat(v_fst_3767_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 2);
lean_ctor_set(v___x_3802_, 0, v___x_3810_);
v___x_3812_ = v___x_3802_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v___x_3812_);
lean_ctor_set(v___x_3807_, 0, v___x_3809_);
v___x_3814_ = v___x_3807_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3798_ == 0)
{
lean_ctor_set(v___x_3797_, 1, v_fst_3777_);
lean_ctor_set(v___x_3797_, 0, v___x_3815_);
v___x_3817_ = v___x_3797_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_fst_3777_);
v___x_3817_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3818_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3819_ = l_Lean_JsonNumber_fromNat(v_fst_3784_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 2);
lean_ctor_set(v___x_3792_, 0, v___x_3819_);
v___x_3821_ = v___x_3792_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3823_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 1, v___x_3821_);
lean_ctor_set(v___x_3787_, 0, v___x_3818_);
v___x_3823_ = v___x_3787_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3825_ = l_Lean_JsonNumber_fromNat(v_numParams_3732_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set_tag(v___x_3775_, 2);
lean_ctor_set(v___x_3775_, 0, v___x_3825_);
v___x_3827_ = v___x_3775_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3825_);
v___x_3827_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
lean_object* v___x_3829_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 1, v___x_3827_);
lean_ctor_set(v___x_3780_, 0, v___x_3824_);
v___x_3829_ = v___x_3780_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3827_);
v___x_3829_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
v___x_3830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_3831_ = l_Lean_JsonNumber_fromNat(v_numIndices_3733_);
v___x_3832_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 1, v___x_3832_);
lean_ctor_set(v___x_3770_, 0, v___x_3830_);
v___x_3834_ = v___x_3770_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3830_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3832_);
v___x_3834_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
lean_ctor_set(v___x_3836_, 1, v_fst_3794_);
v___x_3837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_3838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
lean_ctor_set(v___x_3838_, 1, v_fst_3804_);
v___x_3839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__3));
v___x_3840_ = l_Lean_JsonNumber_fromNat(v_numNested_3736_);
v___x_3841_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3839_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__4));
v___x_3844_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3844_, 0, v_isRec_3737_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__5));
v___x_3847_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3847_, 0, v_isReflexive_3739_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3850_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3850_, 0, v_isUnsafe_3738_);
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3848_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3845_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3842_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3838_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3836_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3834_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3829_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3823_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
v___x_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3817_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3863_, 0, v___x_3814_);
lean_ctor_set(v___x_3863_, 1, v___x_3862_);
v___x_3864_ = l_Lean_Json_mkObj(v___x_3863_);
lean_dec_ref_known(v___x_3863_, 2);
v_fst_3746_ = v___x_3864_;
v_snd_3747_ = v_snd_3805_;
goto v___jp_3745_;
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
else
{
lean_del_object(v___x_3797_);
lean_dec(v_fst_3794_);
lean_del_object(v___x_3792_);
lean_del_object(v___x_3787_);
lean_dec(v_fst_3784_);
lean_del_object(v___x_3780_);
lean_dec(v_fst_3777_);
lean_del_object(v___x_3775_);
lean_del_object(v___x_3770_);
lean_dec(v_fst_3767_);
lean_dec(v_numNested_3736_);
lean_dec(v_numIndices_3733_);
lean_dec(v_numParams_3732_);
v___y_3753_ = v___x_3799_;
goto v___jp_3752_;
}
}
}
}
else
{
lean_del_object(v___x_3787_);
lean_dec(v_fst_3784_);
lean_del_object(v___x_3780_);
lean_dec(v_fst_3777_);
lean_del_object(v___x_3775_);
lean_del_object(v___x_3770_);
lean_dec(v_fst_3767_);
lean_dec(v_numNested_3736_);
lean_dec(v_ctors_3735_);
lean_dec(v_numIndices_3733_);
lean_dec(v_numParams_3732_);
v___y_3753_ = v___x_3789_;
goto v___jp_3752_;
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3780_);
lean_dec(v_fst_3777_);
lean_del_object(v___x_3775_);
lean_del_object(v___x_3770_);
lean_dec(v_fst_3767_);
lean_dec_ref(v_bs_x27_3744_);
lean_dec(v_numNested_3736_);
lean_dec(v_ctors_3735_);
lean_dec(v_all_3734_);
lean_dec(v_numIndices_3733_);
lean_dec(v_numParams_3732_);
v_a_3878_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3782_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3782_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_3770_);
lean_dec(v_fst_3767_);
lean_dec_ref(v_type_3742_);
lean_dec(v_numNested_3736_);
lean_dec(v_ctors_3735_);
lean_dec(v_all_3734_);
lean_dec(v_numIndices_3733_);
lean_dec(v_numParams_3732_);
v___y_3753_ = v___x_3772_;
goto v___jp_3752_;
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_bs_x27_3744_);
lean_dec_ref(v_type_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_numNested_3736_);
lean_dec(v_ctors_3735_);
lean_dec(v_all_3734_);
lean_dec(v_numIndices_3733_);
lean_dec(v_numParams_3732_);
v_a_3889_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3765_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3765_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
v___jp_3745_:
{
size_t v___x_3748_; size_t v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = ((size_t)1ULL);
v___x_3749_ = lean_usize_add(v_i_3722_, v___x_3748_);
v___x_3750_ = lean_array_uset(v_bs_x27_3744_, v_i_3722_, v_fst_3746_);
v_i_3722_ = v___x_3749_;
v_bs_3723_ = v___x_3750_;
v___y_3725_ = v_snd_3747_;
goto _start;
}
v___jp_3752_:
{
if (lean_obj_tag(v___y_3753_) == 0)
{
lean_object* v_a_3754_; lean_object* v_fst_3755_; lean_object* v_snd_3756_; 
v_a_3754_ = lean_ctor_get(v___y_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___y_3753_, 1);
v_fst_3755_ = lean_ctor_get(v_a_3754_, 0);
lean_inc(v_fst_3755_);
v_snd_3756_ = lean_ctor_get(v_a_3754_, 1);
lean_inc(v_snd_3756_);
lean_dec(v_a_3754_);
v_fst_3746_ = v_fst_3755_;
v_snd_3747_ = v_snd_3756_;
goto v___jp_3745_;
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec_ref(v_bs_x27_3744_);
v_a_3757_ = lean_ctor_get(v___y_3753_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___y_3753_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___y_3753_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___y_3753_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3721_ = stack[0].m_num;
size_t v_i_3722_ = stack[1].m_num;
lean_object* v_bs_3723_ = stack[2].m_obj;
lean_object* v___y_3724_ = stack[3].m_obj;
lean_object* v___y_3725_ = stack[4].m_obj;
lean_object* v_res_3897_;
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_3721_, v_i_3722_, v_bs_3723_, v___y_3724_, v___y_3725_);
stack->m_obj
 = v_res_3897_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(size_t v_sz_3901_, size_t v_i_3902_, lean_object* v_bs_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
uint8_t v___x_3907_; 
v___x_3907_ = lean_usize_dec_lt(v_i_3902_, v_sz_3901_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_bs_3903_);
lean_ctor_set(v___x_3908_, 1, v___y_3905_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
else
{
lean_object* v_v_3910_; lean_object* v_toConstantVal_3911_; lean_object* v_induct_3912_; lean_object* v_cidx_3913_; lean_object* v_numParams_3914_; lean_object* v_numFields_3915_; uint8_t v_isUnsafe_3916_; lean_object* v_name_3917_; lean_object* v_levelParams_3918_; lean_object* v_type_3919_; lean_object* v___x_3920_; lean_object* v_bs_x27_3921_; lean_object* v_fst_3923_; lean_object* v_snd_3924_; lean_object* v___x_3929_; 
v_v_3910_ = lean_array_uget_borrowed(v_bs_3903_, v_i_3902_);
v_toConstantVal_3911_ = lean_ctor_get(v_v_3910_, 0);
v_induct_3912_ = lean_ctor_get(v_v_3910_, 1);
lean_inc(v_induct_3912_);
v_cidx_3913_ = lean_ctor_get(v_v_3910_, 2);
lean_inc(v_cidx_3913_);
v_numParams_3914_ = lean_ctor_get(v_v_3910_, 3);
lean_inc(v_numParams_3914_);
v_numFields_3915_ = lean_ctor_get(v_v_3910_, 4);
lean_inc(v_numFields_3915_);
v_isUnsafe_3916_ = lean_ctor_get_uint8(v_v_3910_, sizeof(void*)*5);
v_name_3917_ = lean_ctor_get(v_toConstantVal_3911_, 0);
lean_inc(v_name_3917_);
v_levelParams_3918_ = lean_ctor_get(v_toConstantVal_3911_, 1);
lean_inc(v_levelParams_3918_);
v_type_3919_ = lean_ctor_get(v_toConstantVal_3911_, 2);
lean_inc_ref(v_type_3919_);
v___x_3920_ = lean_unsigned_to_nat(0u);
v_bs_x27_3921_ = lean_array_uset(v_bs_3903_, v_i_3902_, v___x_3920_);
v___x_3929_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_3917_, v___y_3904_, v___y_3905_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; lean_object* v_fst_3931_; lean_object* v_snd_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_4034_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v_fst_3931_ = lean_ctor_get(v_a_3930_, 0);
v_snd_3932_ = lean_ctor_get(v_a_3930_, 1);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_a_3930_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_3934_ = v_a_3930_;
v_isShared_3935_ = v_isSharedCheck_4034_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_snd_3932_);
lean_inc(v_fst_3931_);
lean_dec(v_a_3930_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_4034_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3936_; 
v___x_3936_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_3918_, v___y_3904_, v_snd_3932_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v_fst_3938_; lean_object* v_snd_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_4022_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v_fst_3938_ = lean_ctor_get(v_a_3937_, 0);
v_snd_3939_ = lean_ctor_get(v_a_3937_, 1);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_a_3937_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_3941_ = v_a_3937_;
v_isShared_3942_ = v_isSharedCheck_4022_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_snd_3939_);
lean_inc(v_fst_3938_);
lean_dec(v_a_3937_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_4022_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; 
v___x_3943_ = l_LeanExport_dumpExpr(v_type_3919_, v___y_3904_, v_snd_3939_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4013_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v_fst_3945_ = lean_ctor_get(v_a_3944_, 0);
v_snd_3946_ = lean_ctor_get(v_a_3944_, 1);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_a_3944_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_3948_ = v_a_3944_;
v_isShared_3949_ = v_isSharedCheck_4013_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_snd_3946_);
lean_inc(v_fst_3945_);
lean_dec(v_a_3944_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4013_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_induct_3912_, v___y_3904_, v_snd_3946_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v_fst_3952_; lean_object* v_snd_3953_; lean_object* v___x_3955_; uint8_t v_isShared_3956_; uint8_t v_isSharedCheck_4004_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
v_fst_3952_ = lean_ctor_get(v_a_3951_, 0);
v_snd_3953_ = lean_ctor_get(v_a_3951_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_a_3951_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3955_ = v_a_3951_;
v_isShared_3956_ = v_isSharedCheck_4004_;
goto v_resetjp_3954_;
}
else
{
lean_inc(v_snd_3953_);
lean_inc(v_fst_3952_);
lean_dec(v_a_3951_);
v___x_3955_ = lean_box(0);
v_isShared_3956_ = v_isSharedCheck_4004_;
goto v_resetjp_3954_;
}
v_resetjp_3954_:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_3958_ = l_Lean_JsonNumber_fromNat(v_fst_3931_);
v___x_3959_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
if (v_isShared_3956_ == 0)
{
lean_ctor_set(v___x_3955_, 1, v___x_3959_);
lean_ctor_set(v___x_3955_, 0, v___x_3957_);
v___x_3961_ = v___x_3955_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_4003_, 1, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_4003_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 1, v_fst_3938_);
lean_ctor_set(v___x_3948_, 0, v___x_3962_);
v___x_3964_ = v___x_3948_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_4002_, 1, v_fst_3938_);
v___x_3964_ = v_reuseFailAlloc_4002_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3965_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_3966_ = l_Lean_JsonNumber_fromNat(v_fst_3945_);
v___x_3967_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 1, v___x_3967_);
lean_ctor_set(v___x_3941_, 0, v___x_3965_);
v___x_3969_ = v___x_3941_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3965_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__2));
v___x_3971_ = l_Lean_JsonNumber_fromNat(v_fst_3952_);
v___x_3972_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
if (v_isShared_3935_ == 0)
{
lean_ctor_set(v___x_3934_, 1, v___x_3972_);
lean_ctor_set(v___x_3934_, 0, v___x_3970_);
v___x_3974_ = v___x_3934_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__3));
v___x_3976_ = l_Lean_JsonNumber_fromNat(v_cidx_3913_);
v___x_3977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3975_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
v___x_3979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_3980_ = l_Lean_JsonNumber_fromNat(v_numParams_3914_);
v___x_3981_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3979_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__5));
v___x_3984_ = l_Lean_JsonNumber_fromNat(v_numFields_3915_);
v___x_3985_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3983_);
lean_ctor_set(v___x_3986_, 1, v___x_3985_);
v___x_3987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_3988_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3988_, 0, v_isUnsafe_3916_);
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3987_);
lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = lean_box(0);
v___x_3991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3989_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3986_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3982_);
lean_ctor_set(v___x_3993_, 1, v___x_3992_);
v___x_3994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3978_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3974_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3969_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3964_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3961_);
lean_ctor_set(v___x_3998_, 1, v___x_3997_);
v___x_3999_ = l_Lean_Json_mkObj(v___x_3998_);
lean_dec_ref_known(v___x_3998_, 2);
v_fst_3923_ = v___x_3999_;
v_snd_3924_ = v_snd_3953_;
goto v___jp_3922_;
}
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_del_object(v___x_3948_);
lean_dec(v_fst_3945_);
lean_del_object(v___x_3941_);
lean_dec(v_fst_3938_);
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec(v_numFields_3915_);
lean_dec(v_numParams_3914_);
lean_dec(v_cidx_3913_);
v_a_4005_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3950_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3950_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_del_object(v___x_3941_);
lean_dec(v_fst_3938_);
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_dec_ref(v_bs_x27_3921_);
lean_dec(v_numFields_3915_);
lean_dec(v_numParams_3914_);
lean_dec(v_cidx_3913_);
lean_dec(v_induct_3912_);
v_a_4014_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3943_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3943_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
else
{
lean_del_object(v___x_3934_);
lean_dec(v_fst_3931_);
lean_dec_ref(v_type_3919_);
lean_dec(v_numFields_3915_);
lean_dec(v_numParams_3914_);
lean_dec(v_cidx_3913_);
lean_dec(v_induct_3912_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_4023_; lean_object* v_fst_4024_; lean_object* v_snd_4025_; 
v_a_4023_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_3936_, 1);
v_fst_4024_ = lean_ctor_get(v_a_4023_, 0);
lean_inc(v_fst_4024_);
v_snd_4025_ = lean_ctor_get(v_a_4023_, 1);
lean_inc(v_snd_4025_);
lean_dec(v_a_4023_);
v_fst_3923_ = v_fst_4024_;
v_snd_3924_ = v_snd_4025_;
goto v___jp_3922_;
}
else
{
lean_object* v_a_4026_; lean_object* v___x_4028_; uint8_t v_isShared_4029_; uint8_t v_isSharedCheck_4033_; 
lean_dec_ref(v_bs_x27_3921_);
v_a_4026_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_4033_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_4033_ == 0)
{
v___x_4028_ = v___x_3936_;
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
else
{
lean_inc(v_a_4026_);
lean_dec(v___x_3936_);
v___x_4028_ = lean_box(0);
v_isShared_4029_ = v_isSharedCheck_4033_;
goto v_resetjp_4027_;
}
v_resetjp_4027_:
{
lean_object* v___x_4031_; 
if (v_isShared_4029_ == 0)
{
v___x_4031_ = v___x_4028_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v_a_4026_);
v___x_4031_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
return v___x_4031_;
}
}
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v_bs_x27_3921_);
lean_dec_ref(v_type_3919_);
lean_dec(v_levelParams_3918_);
lean_dec(v_numFields_3915_);
lean_dec(v_numParams_3914_);
lean_dec(v_cidx_3913_);
lean_dec(v_induct_3912_);
v_a_4035_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_3929_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_3929_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
v___jp_3922_:
{
size_t v___x_3925_; size_t v___x_3926_; lean_object* v___x_3927_; 
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3902_, v___x_3925_);
v___x_3927_ = lean_array_uset(v_bs_x27_3921_, v_i_3902_, v_fst_3923_);
v_i_3902_ = v___x_3926_;
v_bs_3903_ = v___x_3927_;
v___y_3905_ = v_snd_3924_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3901_ = stack[0].m_num;
size_t v_i_3902_ = stack[1].m_num;
lean_object* v_bs_3903_ = stack[2].m_obj;
lean_object* v___y_3904_ = stack[3].m_obj;
lean_object* v___y_3905_ = stack[4].m_obj;
lean_object* v_res_4043_;
v_res_4043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_3901_, v_i_3902_, v_bs_3903_, v___y_3904_, v___y_3905_);
stack->m_obj
 = v_res_4043_;
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(lean_object* v_rule_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_ctor_4050_; lean_object* v_nfields_4051_; lean_object* v_rhs_4052_; lean_object* v___x_4053_; 
v_ctor_4050_ = lean_ctor_get(v_rule_4046_, 0);
lean_inc(v_ctor_4050_);
v_nfields_4051_ = lean_ctor_get(v_rule_4046_, 1);
lean_inc(v_nfields_4051_);
v_rhs_4052_ = lean_ctor_get(v_rule_4046_, 2);
lean_inc_ref(v_rhs_4052_);
lean_dec_ref(v_rule_4046_);
v___x_4053_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_ctor_4050_, v_a_4047_, v_a_4048_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v_fst_4055_; lean_object* v_snd_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4105_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v_fst_4055_ = lean_ctor_get(v_a_4054_, 0);
v_snd_4056_ = lean_ctor_get(v_a_4054_, 1);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_a_4054_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4058_ = v_a_4054_;
v_isShared_4059_ = v_isSharedCheck_4105_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_snd_4056_);
lean_inc(v_fst_4055_);
lean_dec(v_a_4054_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4105_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_LeanExport_dumpExpr(v_rhs_4052_, v_a_4047_, v_snd_4056_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4096_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4096_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4096_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_fst_4065_; lean_object* v_snd_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4095_; 
v_fst_4065_ = lean_ctor_get(v_a_4061_, 0);
v_snd_4066_ = lean_ctor_get(v_a_4061_, 1);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_a_4061_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4068_ = v_a_4061_;
v_isShared_4069_ = v_isSharedCheck_4095_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_snd_4066_);
lean_inc(v_fst_4065_);
lean_dec(v_a_4061_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4095_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4070_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__2));
v___x_4071_ = l_Lean_JsonNumber_fromNat(v_fst_4055_);
v___x_4072_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
if (v_isShared_4069_ == 0)
{
lean_ctor_set(v___x_4068_, 1, v___x_4072_);
lean_ctor_set(v___x_4068_, 0, v___x_4070_);
v___x_4074_ = v___x_4068_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4070_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4075_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__0));
v___x_4076_ = l_Lean_JsonNumber_fromNat(v_nfields_4051_);
v___x_4077_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4077_);
lean_ctor_set(v___x_4058_, 0, v___x_4075_);
v___x_4079_ = v___x_4058_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4075_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4080_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___closed__1));
v___x_4081_ = l_Lean_JsonNumber_fromNat(v_fst_4065_);
v___x_4082_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4080_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_box(0);
v___x_4085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4083_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4079_);
lean_ctor_set(v___x_4086_, 1, v___x_4085_);
v___x_4087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4074_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = l_Lean_Json_mkObj(v___x_4087_);
lean_dec_ref_known(v___x_4087_, 2);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v_snd_4066_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4089_);
v___x_4091_ = v___x_4063_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
return v___x_4091_;
}
}
}
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_del_object(v___x_4058_);
lean_dec(v_fst_4055_);
lean_dec(v_nfields_4051_);
v_a_4097_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4060_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4060_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec_ref(v_rhs_4052_);
lean_dec(v_nfields_4051_);
v_a_4106_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4053_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4053_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule_0interp(lean_interpreter_value* stack)
{
lean_object* v_rule_4046_ = stack[0].m_obj;
lean_object* v_a_4047_ = stack[1].m_obj;
lean_object* v_a_4048_ = stack[2].m_obj;
lean_object* v_res_4114_;
v_res_4114_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_4046_, v_a_4047_, v_a_4048_);
stack->m_obj
 = v_res_4114_;
}
lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(lean_object* v_x_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
if (lean_obj_tag(v_x_4115_) == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4120_ = l_List_reverse___redArg(v_x_4116_);
v___x_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v___y_4118_);
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
else
{
lean_object* v_head_4123_; lean_object* v_tail_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4144_; 
v_head_4123_ = lean_ctor_get(v_x_4115_, 0);
v_tail_4124_ = lean_ctor_get(v_x_4115_, 1);
v_isSharedCheck_4144_ = !lean_is_exclusive(v_x_4115_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4126_ = v_x_4115_;
v_isShared_4127_ = v_isSharedCheck_4144_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_tail_4124_);
lean_inc(v_head_4123_);
lean_dec(v_x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4144_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; 
v___x_4128_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_head_4123_, v___y_4117_, v___y_4118_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v___x_4133_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v_fst_4130_ = lean_ctor_get(v_a_4129_, 0);
lean_inc(v_fst_4130_);
v_snd_4131_ = lean_ctor_get(v_a_4129_, 1);
lean_inc(v_snd_4131_);
lean_dec(v_a_4129_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 1, v_x_4116_);
lean_ctor_set(v___x_4126_, 0, v_fst_4130_);
v___x_4133_ = v___x_4126_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_fst_4130_);
lean_ctor_set(v_reuseFailAlloc_4135_, 1, v_x_4116_);
v___x_4133_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
v_x_4115_ = v_tail_4124_;
v_x_4116_ = v___x_4133_;
v___y_4118_ = v_snd_4131_;
goto _start;
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_del_object(v___x_4126_);
lean_dec(v_tail_4124_);
lean_dec(v_x_4116_);
v_a_4136_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4128_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4128_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4115_ = stack[0].m_obj;
lean_object* v_x_4116_ = stack[1].m_obj;
lean_object* v___y_4117_ = stack[2].m_obj;
lean_object* v___y_4118_ = stack[3].m_obj;
lean_object* v_res_4145_;
v_res_4145_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_4115_, v_x_4116_, v___y_4117_, v___y_4118_);
stack->m_obj
 = v_res_4145_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(size_t v_sz_4150_, size_t v_i_4151_, lean_object* v_bs_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
uint8_t v___x_4156_; 
v___x_4156_ = lean_usize_dec_lt(v_i_4151_, v_sz_4150_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v_bs_4152_);
lean_ctor_set(v___x_4157_, 1, v___y_4154_);
v___x_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4157_);
return v___x_4158_;
}
else
{
lean_object* v_v_4159_; lean_object* v_toConstantVal_4160_; lean_object* v_all_4161_; lean_object* v_numParams_4162_; lean_object* v_numIndices_4163_; lean_object* v_numMotives_4164_; lean_object* v_numMinors_4165_; lean_object* v_rules_4166_; uint8_t v_k_4167_; uint8_t v_isUnsafe_4168_; lean_object* v_name_4169_; lean_object* v_levelParams_4170_; lean_object* v_type_4171_; lean_object* v___x_4172_; lean_object* v_bs_x27_4173_; lean_object* v_fst_4175_; lean_object* v_snd_4176_; lean_object* v___y_4182_; lean_object* v___x_4194_; 
v_v_4159_ = lean_array_uget_borrowed(v_bs_4152_, v_i_4151_);
v_toConstantVal_4160_ = lean_ctor_get(v_v_4159_, 0);
v_all_4161_ = lean_ctor_get(v_v_4159_, 1);
lean_inc(v_all_4161_);
v_numParams_4162_ = lean_ctor_get(v_v_4159_, 2);
lean_inc(v_numParams_4162_);
v_numIndices_4163_ = lean_ctor_get(v_v_4159_, 3);
lean_inc(v_numIndices_4163_);
v_numMotives_4164_ = lean_ctor_get(v_v_4159_, 4);
lean_inc(v_numMotives_4164_);
v_numMinors_4165_ = lean_ctor_get(v_v_4159_, 5);
lean_inc(v_numMinors_4165_);
v_rules_4166_ = lean_ctor_get(v_v_4159_, 6);
lean_inc(v_rules_4166_);
v_k_4167_ = lean_ctor_get_uint8(v_v_4159_, sizeof(void*)*7);
v_isUnsafe_4168_ = lean_ctor_get_uint8(v_v_4159_, sizeof(void*)*7 + 1);
v_name_4169_ = lean_ctor_get(v_toConstantVal_4160_, 0);
lean_inc(v_name_4169_);
v_levelParams_4170_ = lean_ctor_get(v_toConstantVal_4160_, 1);
lean_inc(v_levelParams_4170_);
v_type_4171_ = lean_ctor_get(v_toConstantVal_4160_, 2);
lean_inc_ref(v_type_4171_);
v___x_4172_ = lean_unsigned_to_nat(0u);
v_bs_x27_4173_ = lean_array_uset(v_bs_4152_, v_i_4151_, v___x_4172_);
v___x_4194_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4169_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v_fst_4196_; lean_object* v_snd_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4321_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v_fst_4196_ = lean_ctor_get(v_a_4195_, 0);
v_snd_4197_ = lean_ctor_get(v_a_4195_, 1);
v_isSharedCheck_4321_ = !lean_is_exclusive(v_a_4195_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4199_ = v_a_4195_;
v_isShared_4200_ = v_isSharedCheck_4321_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_snd_4197_);
lean_inc(v_fst_4196_);
lean_dec(v_a_4195_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4321_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4170_, v___y_4153_, v_snd_4197_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4320_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4320_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4320_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v_fst_4206_; lean_object* v_snd_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4319_; 
v_fst_4206_ = lean_ctor_get(v_a_4202_, 0);
v_snd_4207_ = lean_ctor_get(v_a_4202_, 1);
v_isSharedCheck_4319_ = !lean_is_exclusive(v_a_4202_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4209_ = v_a_4202_;
v_isShared_4210_ = v_isSharedCheck_4319_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_snd_4207_);
lean_inc(v_fst_4206_);
lean_dec(v_a_4202_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4319_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_LeanExport_dumpExpr(v_type_4171_, v___y_4153_, v_snd_4207_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v_fst_4213_; lean_object* v_snd_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4310_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v_fst_4213_ = lean_ctor_get(v_a_4212_, 0);
v_snd_4214_ = lean_ctor_get(v_a_4212_, 1);
v_isSharedCheck_4310_ = !lean_is_exclusive(v_a_4212_);
if (v_isSharedCheck_4310_ == 0)
{
v___x_4216_ = v_a_4212_;
v_isShared_4217_ = v_isSharedCheck_4310_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_snd_4214_);
lean_inc(v_fst_4213_);
lean_dec(v_a_4212_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4310_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4218_; 
v___x_4218_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_4161_, v___y_4153_, v_snd_4214_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4309_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4309_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4309_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v_fst_4223_; lean_object* v_snd_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4308_; 
v_fst_4223_ = lean_ctor_get(v_a_4219_, 0);
v_snd_4224_ = lean_ctor_get(v_a_4219_, 1);
v_isSharedCheck_4308_ = !lean_is_exclusive(v_a_4219_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4226_ = v_a_4219_;
v_isShared_4227_ = v_isSharedCheck_4308_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_snd_4224_);
lean_inc(v_fst_4223_);
lean_dec(v_a_4219_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4308_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
v___x_4228_ = lean_box(0);
v___x_4229_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_rules_4166_, v___x_4228_, v___y_4153_, v_snd_4224_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v_a_4230_; lean_object* v_fst_4231_; lean_object* v_snd_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4299_; 
v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_a_4230_);
lean_dec_ref_known(v___x_4229_, 1);
v_fst_4231_ = lean_ctor_get(v_a_4230_, 0);
v_snd_4232_ = lean_ctor_get(v_a_4230_, 1);
v_isSharedCheck_4299_ = !lean_is_exclusive(v_a_4230_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4234_ = v_a_4230_;
v_isShared_4235_ = v_isSharedCheck_4299_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_snd_4232_);
lean_inc(v_fst_4231_);
lean_dec(v_a_4230_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4299_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4237_ = l_Lean_JsonNumber_fromNat(v_fst_4196_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set_tag(v___x_4221_, 2);
lean_ctor_set(v___x_4221_, 0, v___x_4237_);
v___x_4239_ = v___x_4221_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
lean_object* v___x_4241_; 
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 1, v___x_4239_);
lean_ctor_set(v___x_4234_, 0, v___x_4236_);
v___x_4241_ = v___x_4234_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v___x_4236_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
v___x_4242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 1, v_fst_4206_);
lean_ctor_set(v___x_4226_, 0, v___x_4242_);
v___x_4244_ = v___x_4226_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4242_);
lean_ctor_set(v_reuseFailAlloc_4296_, 1, v_fst_4206_);
v___x_4244_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4248_; 
v___x_4245_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4246_ = l_Lean_JsonNumber_fromNat(v_fst_4213_);
if (v_isShared_4205_ == 0)
{
lean_ctor_set_tag(v___x_4204_, 2);
lean_ctor_set(v___x_4204_, 0, v___x_4246_);
v___x_4248_ = v___x_4204_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v___x_4246_);
v___x_4248_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
lean_object* v___x_4250_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 1, v___x_4248_);
lean_ctor_set(v___x_4216_, 0, v___x_4245_);
v___x_4250_ = v___x_4216_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4294_; 
v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4245_);
lean_ctor_set(v_reuseFailAlloc_4294_, 1, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4294_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 1, v_fst_4223_);
lean_ctor_set(v___x_4209_, 0, v___x_4251_);
v___x_4253_ = v___x_4209_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_fst_4223_);
v___x_4253_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__4));
v___x_4255_ = l_Lean_JsonNumber_fromNat(v_numParams_4162_);
v___x_4256_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 1, v___x_4256_);
lean_ctor_set(v___x_4199_, 0, v___x_4254_);
v___x_4258_ = v___x_4199_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4254_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__0));
v___x_4260_ = l_Lean_JsonNumber_fromNat(v_numIndices_4163_);
v___x_4261_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4259_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__0));
v___x_4264_ = l_Lean_JsonNumber_fromNat(v_numMotives_4164_);
v___x_4265_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4263_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__1));
v___x_4268_ = l_Lean_JsonNumber_fromNat(v_numMinors_4165_);
v___x_4269_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4267_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__2));
v___x_4272_ = l_Lean_List_toJson___at___00LeanExport_dumpConstant_spec__3(v_fst_4231_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4271_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___closed__3));
v___x_4275_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4275_, 0, v_k_4167_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4278_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4278_, 0, v_isUnsafe_4168_);
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4277_);
lean_ctor_set(v___x_4279_, 1, v___x_4278_);
v___x_4280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
lean_ctor_set(v___x_4280_, 1, v___x_4228_);
v___x_4281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4276_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4273_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4270_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4266_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4262_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4258_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4253_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4250_);
lean_ctor_set(v___x_4288_, 1, v___x_4287_);
v___x_4289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4244_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4241_);
lean_ctor_set(v___x_4290_, 1, v___x_4289_);
v___x_4291_ = l_Lean_Json_mkObj(v___x_4290_);
lean_dec_ref_known(v___x_4290_, 2);
v_fst_4175_ = v___x_4291_;
v_snd_4176_ = v_snd_4232_;
goto v___jp_4174_;
}
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
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_del_object(v___x_4226_);
lean_dec(v_fst_4223_);
lean_del_object(v___x_4221_);
lean_del_object(v___x_4216_);
lean_dec(v_fst_4213_);
lean_del_object(v___x_4209_);
lean_dec(v_fst_4206_);
lean_del_object(v___x_4204_);
lean_del_object(v___x_4199_);
lean_dec(v_fst_4196_);
lean_dec_ref(v_bs_x27_4173_);
lean_dec(v_numMinors_4165_);
lean_dec(v_numMotives_4164_);
lean_dec(v_numIndices_4163_);
lean_dec(v_numParams_4162_);
v_a_4300_ = lean_ctor_get(v___x_4229_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4229_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4229_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4229_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4216_);
lean_dec(v_fst_4213_);
lean_del_object(v___x_4209_);
lean_dec(v_fst_4206_);
lean_del_object(v___x_4204_);
lean_del_object(v___x_4199_);
lean_dec(v_fst_4196_);
lean_dec(v_rules_4166_);
lean_dec(v_numMinors_4165_);
lean_dec(v_numMotives_4164_);
lean_dec(v_numIndices_4163_);
lean_dec(v_numParams_4162_);
v___y_4182_ = v___x_4218_;
goto v___jp_4181_;
}
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_del_object(v___x_4209_);
lean_dec(v_fst_4206_);
lean_del_object(v___x_4204_);
lean_del_object(v___x_4199_);
lean_dec(v_fst_4196_);
lean_dec_ref(v_bs_x27_4173_);
lean_dec(v_rules_4166_);
lean_dec(v_numMinors_4165_);
lean_dec(v_numMotives_4164_);
lean_dec(v_numIndices_4163_);
lean_dec(v_numParams_4162_);
lean_dec(v_all_4161_);
v_a_4311_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4211_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4211_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4199_);
lean_dec(v_fst_4196_);
lean_dec_ref(v_type_4171_);
lean_dec(v_rules_4166_);
lean_dec(v_numMinors_4165_);
lean_dec(v_numMotives_4164_);
lean_dec(v_numIndices_4163_);
lean_dec(v_numParams_4162_);
lean_dec(v_all_4161_);
v___y_4182_ = v___x_4201_;
goto v___jp_4181_;
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v_bs_x27_4173_);
lean_dec_ref(v_type_4171_);
lean_dec(v_levelParams_4170_);
lean_dec(v_rules_4166_);
lean_dec(v_numMinors_4165_);
lean_dec(v_numMotives_4164_);
lean_dec(v_numIndices_4163_);
lean_dec(v_numParams_4162_);
lean_dec(v_all_4161_);
v_a_4322_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4194_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4194_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
v___jp_4174_:
{
size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4151_, v___x_4177_);
v___x_4179_ = lean_array_uset(v_bs_x27_4173_, v_i_4151_, v_fst_4175_);
v_i_4151_ = v___x_4178_;
v_bs_4152_ = v___x_4179_;
v___y_4154_ = v_snd_4176_;
goto _start;
}
v___jp_4181_:
{
if (lean_obj_tag(v___y_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_fst_4184_; lean_object* v_snd_4185_; 
v_a_4183_ = lean_ctor_get(v___y_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___y_4182_, 1);
v_fst_4184_ = lean_ctor_get(v_a_4183_, 0);
lean_inc(v_fst_4184_);
v_snd_4185_ = lean_ctor_get(v_a_4183_, 1);
lean_inc(v_snd_4185_);
lean_dec(v_a_4183_);
v_fst_4175_ = v_fst_4184_;
v_snd_4176_ = v_snd_4185_;
goto v___jp_4174_;
}
else
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref(v_bs_x27_4173_);
v_a_4186_ = lean_ctor_get(v___y_4182_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___y_4182_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___y_4182_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___y_4182_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4150_ = stack[0].m_num;
size_t v_i_4151_ = stack[1].m_num;
lean_object* v_bs_4152_ = stack[2].m_obj;
lean_object* v___y_4153_ = stack[3].m_obj;
lean_object* v___y_4154_ = stack[4].m_obj;
lean_object* v_res_4330_;
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4150_, v_i_4151_, v_bs_4152_, v___y_4153_, v___y_4154_);
stack->m_obj
 = v_res_4330_;
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(uint8_t v___x_4379_, lean_object* v_as_x27_4380_, lean_object* v_b_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
if (lean_obj_tag(v_as_x27_4380_) == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_b_4381_);
lean_ctor_set(v___x_4385_, 1, v___y_4383_);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
else
{
lean_object* v_head_4387_; lean_object* v_tail_4388_; lean_object* v___x_4389_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___x_4420_; 
lean_dec_ref(v_b_4381_);
v_head_4387_ = lean_ctor_get(v_as_x27_4380_, 0);
v_tail_4388_ = lean_ctor_get(v_as_x27_4380_, 1);
v___x_4389_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
lean_inc(v_head_4387_);
lean_inc_ref(v___y_4382_);
v___x_4420_ = l_Lean_Environment_find_x3f(v___y_4382_, v_head_4387_, v___x_4379_);
if (lean_obj_tag(v___x_4420_) == 1)
{
lean_object* v_val_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4544_; 
v_val_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4544_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_val_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4544_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
if (lean_obj_tag(v_val_4421_) == 4)
{
lean_object* v_val_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4543_; 
v_val_4425_ = lean_ctor_get(v_val_4421_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_val_4421_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4427_ = v_val_4421_;
v_isShared_4428_ = v_isSharedCheck_4543_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_val_4425_);
lean_dec(v_val_4421_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4543_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_toConstantVal_4429_; lean_object* v_visitedNames_4430_; lean_object* v_visitedLevels_4431_; lean_object* v_visitedExprs_4432_; lean_object* v_visitedConstants_4433_; lean_object* v_noMDataExprs_4434_; uint8_t v_exportMData_4435_; uint8_t v_exportUnsafe_4436_; uint8_t v_ignoreMissing_4437_; lean_object* v_recursorMap_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4542_; 
v_toConstantVal_4429_ = lean_ctor_get(v_val_4425_, 0);
lean_inc_ref(v_toConstantVal_4429_);
v_visitedNames_4430_ = lean_ctor_get(v___y_4383_, 0);
v_visitedLevels_4431_ = lean_ctor_get(v___y_4383_, 1);
v_visitedExprs_4432_ = lean_ctor_get(v___y_4383_, 2);
v_visitedConstants_4433_ = lean_ctor_get(v___y_4383_, 3);
v_noMDataExprs_4434_ = lean_ctor_get(v___y_4383_, 4);
v_exportMData_4435_ = lean_ctor_get_uint8(v___y_4383_, sizeof(void*)*6);
v_exportUnsafe_4436_ = lean_ctor_get_uint8(v___y_4383_, sizeof(void*)*6 + 1);
v_ignoreMissing_4437_ = lean_ctor_get_uint8(v___y_4383_, sizeof(void*)*6 + 2);
v_recursorMap_4438_ = lean_ctor_get(v___y_4383_, 5);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___y_4383_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4440_ = v___y_4383_;
v_isShared_4441_ = v_isSharedCheck_4542_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_recursorMap_4438_);
lean_inc(v_noMDataExprs_4434_);
lean_inc(v_visitedConstants_4433_);
lean_inc(v_visitedExprs_4432_);
lean_inc(v_visitedLevels_4431_);
lean_inc(v_visitedNames_4430_);
lean_dec(v___y_4383_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4542_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
uint8_t v_kind_4442_; lean_object* v_name_4443_; lean_object* v_levelParams_4444_; lean_object* v_type_4445_; lean_object* v___x_4446_; lean_object* v___x_4448_; 
v_kind_4442_ = lean_ctor_get_uint8(v_val_4425_, sizeof(void*)*1);
lean_dec_ref(v_val_4425_);
v_name_4443_ = lean_ctor_get(v_toConstantVal_4429_, 0);
lean_inc(v_name_4443_);
v_levelParams_4444_ = lean_ctor_get(v_toConstantVal_4429_, 1);
lean_inc(v_levelParams_4444_);
v_type_4445_ = lean_ctor_get(v_toConstantVal_4429_, 2);
lean_inc_ref(v_type_4445_);
lean_dec_ref(v_toConstantVal_4429_);
lean_inc(v_head_4387_);
v___x_4446_ = l_Lean_NameHashSet_insert(v_visitedConstants_4433_, v_head_4387_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 3, v___x_4446_);
v___x_4448_ = v___x_4440_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_visitedNames_4430_);
lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_visitedLevels_4431_);
lean_ctor_set(v_reuseFailAlloc_4541_, 2, v_visitedExprs_4432_);
lean_ctor_set(v_reuseFailAlloc_4541_, 3, v___x_4446_);
lean_ctor_set(v_reuseFailAlloc_4541_, 4, v_noMDataExprs_4434_);
lean_ctor_set(v_reuseFailAlloc_4541_, 5, v_recursorMap_4438_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*6, v_exportMData_4435_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*6 + 1, v_exportUnsafe_4436_);
lean_ctor_set_uint8(v_reuseFailAlloc_4541_, sizeof(void*)*6 + 2, v_ignoreMissing_4437_);
v___x_4448_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; 
v___x_4449_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4443_, v___y_4382_, v___x_4448_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v_fst_4451_; lean_object* v_snd_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4532_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v_fst_4451_ = lean_ctor_get(v_a_4450_, 0);
v_snd_4452_ = lean_ctor_get(v_a_4450_, 1);
v_isSharedCheck_4532_ = !lean_is_exclusive(v_a_4450_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4454_ = v_a_4450_;
v_isShared_4455_ = v_isSharedCheck_4532_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_snd_4452_);
lean_inc(v_fst_4451_);
lean_dec(v_a_4450_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4532_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; 
v___x_4456_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4444_, v___y_4382_, v_snd_4452_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v_fst_4458_; lean_object* v_snd_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4523_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v_fst_4458_ = lean_ctor_get(v_a_4457_, 0);
v_snd_4459_ = lean_ctor_get(v_a_4457_, 1);
v_isSharedCheck_4523_ = !lean_is_exclusive(v_a_4457_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4461_ = v_a_4457_;
v_isShared_4462_ = v_isSharedCheck_4523_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_snd_4459_);
lean_inc(v_fst_4458_);
lean_dec(v_a_4457_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4523_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4463_; 
v___x_4463_ = l_LeanExport_dumpExpr(v_type_4445_, v___y_4382_, v_snd_4459_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v_fst_4465_; lean_object* v_snd_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4514_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v_fst_4465_ = lean_ctor_get(v_a_4464_, 0);
v_snd_4466_ = lean_ctor_get(v_a_4464_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_a_4464_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4468_ = v_a_4464_;
v_isShared_4469_ = v_isSharedCheck_4514_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_snd_4466_);
lean_inc(v_fst_4465_);
lean_dec(v_a_4464_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4514_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4474_; 
v___x_4470_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__5));
v___x_4471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4472_ = l_Lean_JsonNumber_fromNat(v_fst_4451_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 2);
lean_ctor_set(v___x_4427_, 0, v___x_4472_);
v___x_4474_ = v___x_4427_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4472_);
v___x_4474_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
lean_object* v___x_4476_; 
if (v_isShared_4469_ == 0)
{
lean_ctor_set(v___x_4468_, 1, v___x_4474_);
lean_ctor_set(v___x_4468_, 0, v___x_4471_);
v___x_4476_ = v___x_4468_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4471_);
lean_ctor_set(v_reuseFailAlloc_4512_, 1, v___x_4474_);
v___x_4476_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 1, v_fst_4458_);
lean_ctor_set(v___x_4461_, 0, v___x_4477_);
v___x_4479_ = v___x_4461_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4477_);
lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_fst_4458_);
v___x_4479_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v___x_4480_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4481_ = l_Lean_JsonNumber_fromNat(v_fst_4465_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 2);
lean_ctor_set(v___x_4423_, 0, v___x_4481_);
v___x_4483_ = v___x_4423_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4485_; 
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 1, v___x_4483_);
lean_ctor_set(v___x_4454_, 0, v___x_4480_);
v___x_4485_ = v___x_4454_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4480_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4486_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__6));
v___x_4487_ = l___private_LeanExport_Basic_0__Lean_QuotKind_toJson(v_kind_4442_);
v___x_4488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4486_);
lean_ctor_set(v___x_4488_, 1, v___x_4487_);
v___x_4489_ = lean_box(0);
v___x_4490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4488_);
lean_ctor_set(v___x_4490_, 1, v___x_4489_);
v___x_4491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4485_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
v___x_4492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4479_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4476_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = l_Lean_Json_mkObj(v___x_4493_);
lean_dec_ref_known(v___x_4493_, 2);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4470_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4495_);
lean_ctor_set(v___x_4496_, 1, v___x_4489_);
v___x_4497_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4496_, v_snd_4466_);
lean_dec_ref_known(v___x_4496_, 2);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v_snd_4499_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v_snd_4499_ = lean_ctor_get(v_a_4498_, 1);
lean_inc(v_snd_4499_);
lean_dec(v_a_4498_);
v_as_x27_4380_ = v_tail_4388_;
v_b_4381_ = v___x_4389_;
v___y_4383_ = v_snd_4499_;
goto _start;
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
v_a_4501_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4497_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4497_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
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
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_del_object(v___x_4461_);
lean_dec(v_fst_4458_);
lean_del_object(v___x_4454_);
lean_dec(v_fst_4451_);
lean_del_object(v___x_4427_);
lean_del_object(v___x_4423_);
v_a_4515_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4463_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4463_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
else
{
lean_object* v_a_4524_; lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
lean_del_object(v___x_4454_);
lean_dec(v_fst_4451_);
lean_dec_ref(v_type_4445_);
lean_del_object(v___x_4427_);
lean_del_object(v___x_4423_);
v_a_4524_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4526_ = v___x_4456_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_inc(v_a_4524_);
lean_dec(v___x_4456_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec_ref(v_type_4445_);
lean_dec(v_levelParams_4444_);
lean_del_object(v___x_4427_);
lean_del_object(v___x_4423_);
v_a_4533_ = lean_ctor_get(v___x_4449_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4449_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4449_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4423_);
lean_dec(v_val_4421_);
v___y_4391_ = v___y_4382_;
v___y_4392_ = v___y_4383_;
goto v___jp_4390_;
}
}
}
else
{
lean_dec(v___x_4420_);
v___y_4391_ = v___y_4382_;
v___y_4392_ = v___y_4383_;
goto v___jp_4390_;
}
v___jp_4390_:
{
uint8_t v_ignoreMissing_4393_; 
v_ignoreMissing_4393_ = lean_ctor_get_uint8(v___y_4392_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_4393_ == 0)
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4394_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4395_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4396_ = lean_unsigned_to_nat(313u);
v___x_4397_ = lean_unsigned_to_nat(52u);
v___x_4398_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_4399_ = 1;
lean_inc(v_head_4387_);
v___x_4400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_head_4387_, v___x_4399_);
v___x_4401_ = lean_string_append(v___x_4398_, v___x_4400_);
lean_dec_ref(v___x_4400_);
v___x_4402_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_4403_ = lean_string_append(v___x_4401_, v___x_4402_);
v___x_4404_ = l_mkPanicMessageWithDecl(v___x_4394_, v___x_4395_, v___x_4396_, v___x_4397_, v___x_4403_);
lean_dec_ref(v___x_4403_);
v___x_4405_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_4404_, v___y_4391_, v___y_4392_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v_snd_4407_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref_known(v___x_4405_, 1);
v_snd_4407_ = lean_ctor_get(v_a_4406_, 1);
lean_inc(v_snd_4407_);
lean_dec(v_a_4406_);
v_as_x27_4380_ = v_tail_4388_;
v_b_4381_ = v___x_4389_;
v___y_4383_ = v_snd_4407_;
goto _start;
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
v_a_4409_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4405_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4405_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__4));
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
lean_ctor_set(v___x_4418_, 1, v___y_4392_);
v___x_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4418_);
return v___x_4419_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4379_ = stack[0].m_num;
lean_object* v_as_x27_4380_ = stack[1].m_obj;
lean_object* v_b_4381_ = stack[2].m_obj;
lean_object* v___y_4382_ = stack[3].m_obj;
lean_object* v___y_4383_ = stack[4].m_obj;
lean_object* v_res_4545_;
v_res_4545_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4379_, v_as_x27_4380_, v_b_4381_, v___y_4382_, v___y_4383_);
stack->m_obj
 = v_res_4545_;
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__21(void){
_start:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = l_Lean_NameSet_empty;
v___x_4549_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4550_, 0, v___x_4549_);
lean_ctor_set(v___x_4550_, 1, v___x_4548_);
return v___x_4550_;
}
}
static lean_object* _init_l_LeanExport_dumpConstant___closed__22(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
v___x_4551_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__21, &l_LeanExport_dumpConstant___closed__21_once, _init_l_LeanExport_dumpConstant___closed__21);
v___x_4552_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v___x_4551_);
return v___x_4553_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4556_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__1));
v___x_4557_ = lean_unsigned_to_nat(11u);
v___x_4558_ = lean_unsigned_to_nat(341u);
v___x_4559_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4560_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4561_ = l_mkPanicMessageWithDecl(v___x_4560_, v___x_4559_, v___x_4558_, v___x_4557_, v___x_4556_);
return v___x_4561_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4563_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__3));
v___x_4564_ = lean_unsigned_to_nat(6u);
v___x_4565_ = lean_unsigned_to_nat(329u);
v___x_4566_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_4567_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_4568_ = l_mkPanicMessageWithDecl(v___x_4567_, v___x_4566_, v___x_4565_, v___x_4564_, v___x_4563_);
return v___x_4568_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(uint8_t v___x_4569_, lean_object* v_val_4570_, lean_object* v_as_x27_4571_, lean_object* v_b_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
if (lean_obj_tag(v_as_x27_4571_) == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4576_, 0, v_b_4572_);
lean_ctor_set(v___x_4576_, 1, v___y_4574_);
v___x_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___x_4576_);
return v___x_4577_;
}
else
{
lean_object* v_head_4578_; lean_object* v_tail_4579_; lean_object* v___y_4581_; lean_object* v_snd_4612_; lean_object* v_fst_4613_; lean_object* v_fst_4614_; lean_object* v_snd_4615_; lean_object* v___y_4617_; uint8_t v___y_4618_; lean_object* v___y_4699_; lean_object* v___x_4706_; 
v_head_4578_ = lean_ctor_get(v_as_x27_4571_, 0);
v_tail_4579_ = lean_ctor_get(v_as_x27_4571_, 1);
v_snd_4612_ = lean_ctor_get(v_b_4572_, 1);
lean_inc(v_snd_4612_);
v_fst_4613_ = lean_ctor_get(v_b_4572_, 0);
lean_inc(v_fst_4613_);
lean_dec_ref(v_b_4572_);
v_fst_4614_ = lean_ctor_get(v_snd_4612_, 0);
lean_inc(v_fst_4614_);
v_snd_4615_ = lean_ctor_get(v_snd_4612_, 1);
lean_inc(v_snd_4615_);
lean_dec(v_snd_4612_);
lean_inc(v_head_4578_);
lean_inc_ref(v___y_4573_);
v___x_4706_ = l_Lean_Environment_find_x3f(v___y_4573_, v_head_4578_, v___x_4569_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__8);
v___x_4708_ = l_panic___at___00LeanExport_dumpConstant_spec__6(v___x_4707_);
v___y_4699_ = v___x_4708_;
goto v___jp_4698_;
}
else
{
lean_object* v_val_4709_; 
v_val_4709_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_val_4709_);
lean_dec_ref_known(v___x_4706_, 1);
v___y_4699_ = v_val_4709_;
goto v___jp_4698_;
}
v___jp_4580_:
{
if (lean_obj_tag(v___y_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4603_; 
v_a_4582_ = lean_ctor_get(v___y_4581_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___y_4581_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4584_ = v___y_4581_;
v_isShared_4585_ = v_isSharedCheck_4603_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___y_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4603_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v_fst_4586_; 
v_fst_4586_ = lean_ctor_get(v_a_4582_, 0);
lean_inc(v_fst_4586_);
if (lean_obj_tag(v_fst_4586_) == 0)
{
lean_object* v_snd_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4598_; 
v_snd_4587_ = lean_ctor_get(v_a_4582_, 1);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_a_4582_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v_a_4582_, 0);
lean_dec(v_unused_4599_);
v___x_4589_ = v_a_4582_;
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_snd_4587_);
lean_dec(v_a_4582_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v_a_4591_; lean_object* v___x_4593_; 
v_a_4591_ = lean_ctor_get(v_fst_4586_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v_fst_4586_, 1);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v_a_4591_);
v___x_4593_ = v___x_4589_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_snd_4587_);
v___x_4593_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4595_; 
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4593_);
v___x_4595_ = v___x_4584_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
}
}
else
{
lean_object* v_snd_4600_; lean_object* v_a_4601_; 
lean_del_object(v___x_4584_);
v_snd_4600_ = lean_ctor_get(v_a_4582_, 1);
lean_inc(v_snd_4600_);
lean_dec(v_a_4582_);
v_a_4601_ = lean_ctor_get(v_fst_4586_, 0);
lean_inc(v_a_4601_);
lean_dec_ref_known(v_fst_4586_, 1);
v_as_x27_4571_ = v_tail_4579_;
v_b_4572_ = v_a_4601_;
v___y_4574_ = v_snd_4600_;
goto _start;
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
v_a_4604_ = lean_ctor_get(v___y_4581_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___y_4581_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___y_4581_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___y_4581_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
v___jp_4616_:
{
lean_object* v_toConstantVal_4619_; lean_object* v_ctors_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; 
v_toConstantVal_4619_ = lean_ctor_get(v___y_4617_, 0);
lean_inc_ref(v_toConstantVal_4619_);
v_ctors_4620_ = lean_ctor_get(v___y_4617_, 4);
lean_inc(v_ctors_4620_);
v___x_4621_ = lean_array_push(v_fst_4613_, v___y_4617_);
v___x_4622_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_4618_, v___x_4569_, v_ctors_4620_, v_fst_4614_, v___y_4573_, v___y_4574_);
lean_dec(v_ctors_4620_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v_snd_4624_; lean_object* v_fst_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4689_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref_known(v___x_4622_, 1);
v_snd_4624_ = lean_ctor_get(v_a_4623_, 1);
v_fst_4625_ = lean_ctor_get(v_a_4623_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v_a_4623_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4627_ = v_a_4623_;
v_isShared_4628_ = v_isSharedCheck_4689_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_snd_4624_);
lean_inc(v_fst_4625_);
lean_dec(v_a_4623_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4689_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v_visitedNames_4629_; lean_object* v_visitedLevels_4630_; lean_object* v_visitedExprs_4631_; lean_object* v_visitedConstants_4632_; lean_object* v_noMDataExprs_4633_; uint8_t v_exportMData_4634_; uint8_t v_exportUnsafe_4635_; uint8_t v_ignoreMissing_4636_; lean_object* v_recursorMap_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4688_; 
v_visitedNames_4629_ = lean_ctor_get(v_snd_4624_, 0);
v_visitedLevels_4630_ = lean_ctor_get(v_snd_4624_, 1);
v_visitedExprs_4631_ = lean_ctor_get(v_snd_4624_, 2);
v_visitedConstants_4632_ = lean_ctor_get(v_snd_4624_, 3);
v_noMDataExprs_4633_ = lean_ctor_get(v_snd_4624_, 4);
v_exportMData_4634_ = lean_ctor_get_uint8(v_snd_4624_, sizeof(void*)*6);
v_exportUnsafe_4635_ = lean_ctor_get_uint8(v_snd_4624_, sizeof(void*)*6 + 1);
v_ignoreMissing_4636_ = lean_ctor_get_uint8(v_snd_4624_, sizeof(void*)*6 + 2);
v_recursorMap_4637_ = lean_ctor_get(v_snd_4624_, 5);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_snd_4624_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4639_ = v_snd_4624_;
v_isShared_4640_ = v_isSharedCheck_4688_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_recursorMap_4637_);
lean_inc(v_noMDataExprs_4633_);
lean_inc(v_visitedConstants_4632_);
lean_inc(v_visitedExprs_4631_);
lean_inc(v_visitedLevels_4630_);
lean_inc(v_visitedNames_4629_);
lean_dec(v_snd_4624_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4688_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v_type_4641_; lean_object* v___x_4642_; lean_object* v___x_4644_; 
v_type_4641_ = lean_ctor_get(v_toConstantVal_4619_, 2);
lean_inc_ref(v_type_4641_);
lean_dec_ref(v_toConstantVal_4619_);
lean_inc(v_head_4578_);
v___x_4642_ = l_Lean_NameHashSet_insert(v_visitedConstants_4632_, v_head_4578_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 3, v___x_4642_);
v___x_4644_ = v___x_4639_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_visitedNames_4629_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v_visitedLevels_4630_);
lean_ctor_set(v_reuseFailAlloc_4687_, 2, v_visitedExprs_4631_);
lean_ctor_set(v_reuseFailAlloc_4687_, 3, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4687_, 4, v_noMDataExprs_4633_);
lean_ctor_set(v_reuseFailAlloc_4687_, 5, v_recursorMap_4637_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6, v_exportMData_4634_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6 + 1, v_exportUnsafe_4635_);
lean_ctor_set_uint8(v_reuseFailAlloc_4687_, sizeof(void*)*6 + 2, v_ignoreMissing_4636_);
v___x_4644_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; 
v___x_4645_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4641_, v___y_4573_, v___x_4644_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v_snd_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4677_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v_snd_4647_ = lean_ctor_get(v_a_4646_, 1);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_a_4646_);
if (v_isSharedCheck_4677_ == 0)
{
lean_object* v_unused_4678_; 
v_unused_4678_ = lean_ctor_get(v_a_4646_, 0);
lean_dec(v_unused_4678_);
v___x_4649_ = v_a_4646_;
v_isShared_4650_ = v_isSharedCheck_4677_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_snd_4647_);
lean_dec(v_a_4646_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4677_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v_toConstantVal_4651_; lean_object* v_recursorMap_4652_; lean_object* v_name_4653_; lean_object* v___x_4654_; 
v_toConstantVal_4651_ = lean_ctor_get(v_val_4570_, 0);
v_recursorMap_4652_ = lean_ctor_get(v_snd_4647_, 5);
v_name_4653_ = lean_ctor_get(v_toConstantVal_4651_, 0);
v___x_4654_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_recursorMap_4652_, v_name_4653_);
if (lean_obj_tag(v___x_4654_) == 1)
{
lean_object* v_val_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v_val_4655_ = lean_ctor_get(v___x_4654_, 0);
lean_inc(v_val_4655_);
lean_dec_ref_known(v___x_4654_, 1);
v___x_4656_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__0));
v___x_4657_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___x_4656_, v_snd_4615_, v_val_4655_);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v___x_4657_);
lean_ctor_set(v___x_4649_, 0, v_fst_4625_);
v___x_4659_ = v___x_4649_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_fst_4625_);
lean_ctor_set(v_reuseFailAlloc_4664_, 1, v___x_4657_);
v___x_4659_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4661_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 1, v___x_4659_);
lean_ctor_set(v___x_4627_, 0, v___x_4621_);
v___x_4661_ = v___x_4627_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4663_, 1, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
v_as_x27_4571_ = v_tail_4579_;
v_b_4572_ = v___x_4661_;
v___y_4574_ = v_snd_4647_;
goto _start;
}
}
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
lean_dec(v___x_4654_);
v___x_4665_ = lean_array_get_size(v_fst_4625_);
v___x_4666_ = lean_unsigned_to_nat(0u);
v___x_4667_ = lean_nat_dec_eq(v___x_4665_, v___x_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; 
lean_del_object(v___x_4649_);
lean_del_object(v___x_4627_);
lean_dec(v_fst_4625_);
lean_dec_ref(v___x_4621_);
lean_dec(v_snd_4615_);
v___x_4668_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__2);
v___x_4669_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4668_, v___y_4573_, v_snd_4647_);
v___y_4581_ = v___x_4669_;
goto v___jp_4580_;
}
else
{
lean_object* v___x_4671_; 
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 1, v_snd_4615_);
lean_ctor_set(v___x_4649_, 0, v_fst_4625_);
v___x_4671_ = v___x_4649_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_fst_4625_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_snd_4615_);
v___x_4671_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
lean_object* v___x_4673_; 
if (v_isShared_4628_ == 0)
{
lean_ctor_set(v___x_4627_, 1, v___x_4671_);
lean_ctor_set(v___x_4627_, 0, v___x_4621_);
v___x_4673_ = v___x_4627_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v___x_4671_);
v___x_4673_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
v_as_x27_4571_ = v_tail_4579_;
v_b_4572_ = v___x_4673_;
v___y_4574_ = v_snd_4647_;
goto _start;
}
}
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_del_object(v___x_4627_);
lean_dec(v_fst_4625_);
lean_dec_ref(v___x_4621_);
lean_dec(v_snd_4615_);
v_a_4679_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4645_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4645_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
lean_dec_ref(v___x_4621_);
lean_dec_ref(v_toConstantVal_4619_);
lean_dec(v_snd_4615_);
v_a_4690_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4692_ = v___x_4622_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4622_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
v___jp_4698_:
{
lean_object* v___x_4700_; uint8_t v_isUnsafe_4701_; 
v___x_4700_ = l_Lean_ConstantInfo_inductiveVal_x21(v___y_4699_);
lean_dec_ref(v___y_4699_);
v_isUnsafe_4701_ = lean_ctor_get_uint8(v___x_4700_, sizeof(void*)*6 + 1);
if (v_isUnsafe_4701_ == 0)
{
uint8_t v___x_4702_; 
v___x_4702_ = 1;
v___y_4617_ = v___x_4700_;
v___y_4618_ = v___x_4702_;
goto v___jp_4616_;
}
else
{
if (v___x_4569_ == 0)
{
uint8_t v_exportUnsafe_4703_; 
v_exportUnsafe_4703_ = lean_ctor_get_uint8(v___y_4574_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_4703_ == 0)
{
lean_object* v___x_4704_; lean_object* v___x_4705_; 
lean_dec_ref(v___x_4700_);
lean_dec(v_snd_4615_);
lean_dec(v_fst_4614_);
lean_dec(v_fst_4613_);
v___x_4704_ = lean_obj_once(&l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4, &l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___closed__4);
v___x_4705_ = l_panic___at___00LeanExport_dumpConstant_spec__11(v___x_4704_, v___y_4573_, v___y_4574_);
v___y_4581_ = v___x_4705_;
goto v___jp_4580_;
}
else
{
v___y_4617_ = v___x_4700_;
v___y_4618_ = v_exportUnsafe_4703_;
goto v___jp_4616_;
}
}
else
{
v___y_4617_ = v___x_4700_;
v___y_4618_ = v___x_4569_;
goto v___jp_4616_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4569_ = stack[0].m_num;
lean_object* v_val_4570_ = stack[1].m_obj;
lean_object* v_as_x27_4571_ = stack[2].m_obj;
lean_object* v_b_4572_ = stack[3].m_obj;
lean_object* v___y_4573_ = stack[4].m_obj;
lean_object* v___y_4574_ = stack[5].m_obj;
lean_object* v_res_4710_;
v_res_4710_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4569_, v_val_4570_, v_as_x27_4571_, v_b_4572_, v___y_4573_, v___y_4574_);
stack->m_obj
 = v_res_4710_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(lean_object* v_as_4711_, size_t v_sz_4712_, size_t v_i_4713_, lean_object* v_b_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
uint8_t v___x_4718_; 
v___x_4718_ = lean_usize_dec_lt(v_i_4713_, v_sz_4712_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4719_, 0, v_b_4714_);
lean_ctor_set(v___x_4719_, 1, v___y_4716_);
v___x_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
return v___x_4720_;
}
else
{
lean_object* v_visitedNames_4721_; lean_object* v_visitedLevels_4722_; lean_object* v_visitedExprs_4723_; lean_object* v_visitedConstants_4724_; lean_object* v_noMDataExprs_4725_; uint8_t v_exportMData_4726_; uint8_t v_exportUnsafe_4727_; uint8_t v_ignoreMissing_4728_; lean_object* v_recursorMap_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4748_; 
v_visitedNames_4721_ = lean_ctor_get(v___y_4716_, 0);
v_visitedLevels_4722_ = lean_ctor_get(v___y_4716_, 1);
v_visitedExprs_4723_ = lean_ctor_get(v___y_4716_, 2);
v_visitedConstants_4724_ = lean_ctor_get(v___y_4716_, 3);
v_noMDataExprs_4725_ = lean_ctor_get(v___y_4716_, 4);
v_exportMData_4726_ = lean_ctor_get_uint8(v___y_4716_, sizeof(void*)*6);
v_exportUnsafe_4727_ = lean_ctor_get_uint8(v___y_4716_, sizeof(void*)*6 + 1);
v_ignoreMissing_4728_ = lean_ctor_get_uint8(v___y_4716_, sizeof(void*)*6 + 2);
v_recursorMap_4729_ = lean_ctor_get(v___y_4716_, 5);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___y_4716_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4731_ = v___y_4716_;
v_isShared_4732_ = v_isSharedCheck_4748_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_recursorMap_4729_);
lean_inc(v_noMDataExprs_4725_);
lean_inc(v_visitedConstants_4724_);
lean_inc(v_visitedExprs_4723_);
lean_inc(v_visitedLevels_4722_);
lean_inc(v_visitedNames_4721_);
lean_dec(v___y_4716_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4748_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v_a_4733_; lean_object* v_toConstantVal_4734_; lean_object* v_name_4735_; lean_object* v_type_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4740_; 
v_a_4733_ = lean_array_uget_borrowed(v_as_4711_, v_i_4713_);
v_toConstantVal_4734_ = lean_ctor_get(v_a_4733_, 0);
v_name_4735_ = lean_ctor_get(v_toConstantVal_4734_, 0);
v_type_4736_ = lean_ctor_get(v_toConstantVal_4734_, 2);
v___x_4737_ = lean_box(0);
lean_inc(v_name_4735_);
v___x_4738_ = l_Lean_NameHashSet_insert(v_visitedConstants_4724_, v_name_4735_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 3, v___x_4738_);
v___x_4740_ = v___x_4731_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_visitedNames_4721_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_visitedLevels_4722_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_visitedExprs_4723_);
lean_ctor_set(v_reuseFailAlloc_4747_, 3, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4747_, 4, v_noMDataExprs_4725_);
lean_ctor_set(v_reuseFailAlloc_4747_, 5, v_recursorMap_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4747_, sizeof(void*)*6, v_exportMData_4726_);
lean_ctor_set_uint8(v_reuseFailAlloc_4747_, sizeof(void*)*6 + 1, v_exportUnsafe_4727_);
lean_ctor_set_uint8(v_reuseFailAlloc_4747_, sizeof(void*)*6 + 2, v_ignoreMissing_4728_);
v___x_4740_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4741_; 
lean_inc_ref(v_type_4736_);
v___x_4741_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4736_, v___y_4715_, v___x_4740_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v_snd_4743_; size_t v___x_4744_; size_t v___x_4745_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
v_snd_4743_ = lean_ctor_get(v_a_4742_, 1);
lean_inc(v_snd_4743_);
lean_dec(v_a_4742_);
v___x_4744_ = ((size_t)1ULL);
v___x_4745_ = lean_usize_add(v_i_4713_, v___x_4744_);
v_i_4713_ = v___x_4745_;
v_b_4714_ = v___x_4737_;
v___y_4716_ = v_snd_4743_;
goto _start;
}
else
{
return v___x_4741_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4711_ = stack[0].m_obj;
size_t v_sz_4712_ = stack[1].m_num;
size_t v_i_4713_ = stack[2].m_num;
lean_object* v_b_4714_ = stack[3].m_obj;
lean_object* v___y_4715_ = stack[4].m_obj;
lean_object* v___y_4716_ = stack[5].m_obj;
lean_object* v_res_4749_;
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_as_4711_, v_sz_4712_, v_i_4713_, v_b_4714_, v___y_4715_, v___y_4716_);
stack->m_obj
 = v_res_4749_;
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(lean_object* v_as_x27_4750_, lean_object* v_b_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_){
_start:
{
if (lean_obj_tag(v_as_x27_4750_) == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
v___x_4755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4755_, 0, v_b_4751_);
lean_ctor_set(v___x_4755_, 1, v___y_4753_);
v___x_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4755_);
return v___x_4756_;
}
else
{
lean_object* v_head_4757_; lean_object* v_tail_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v_head_4757_ = lean_ctor_get(v_as_x27_4750_, 0);
v_tail_4758_ = lean_ctor_get(v_as_x27_4750_, 1);
v___x_4759_ = lean_box(0);
lean_inc(v_head_4757_);
v___x_4760_ = l_LeanExport_dumpConstant(v_head_4757_, v___y_4752_, v___y_4753_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v_snd_4762_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v_snd_4762_ = lean_ctor_get(v_a_4761_, 1);
lean_inc(v_snd_4762_);
lean_dec(v_a_4761_);
v_as_x27_4750_ = v_tail_4758_;
v_b_4751_ = v___x_4759_;
v___y_4753_ = v_snd_4762_;
goto _start;
}
else
{
return v___x_4760_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_4750_ = stack[0].m_obj;
lean_object* v_b_4751_ = stack[1].m_obj;
lean_object* v___y_4752_ = stack[2].m_obj;
lean_object* v___y_4753_ = stack[3].m_obj;
lean_object* v_res_4764_;
v_res_4764_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_4750_, v_b_4751_, v___y_4752_, v___y_4753_);
stack->m_obj
 = v_res_4764_;
}
lean_object* l_LeanExport_dumpConstant(lean_object* v_c_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v_fst_4777_; lean_object* v_snd_4778_; uint8_t v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = 0;
lean_inc(v_c_4765_);
lean_inc_ref(v_a_4766_);
v___x_4876_ = l_Lean_Environment_find_x3f(v_a_4766_, v_c_4765_, v___x_4875_);
if (lean_obj_tag(v___x_4876_) == 1)
{
lean_object* v_val_4877_; uint8_t v___y_5616_; uint8_t v___x_5617_; 
v_val_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_val_4877_);
lean_dec_ref_known(v___x_4876_, 1);
v___x_5617_ = l_Lean_ConstantInfo_isUnsafe(v_val_4877_);
if (v___x_5617_ == 0)
{
v___y_5616_ = v___x_5617_;
goto v___jp_5615_;
}
else
{
uint8_t v_exportUnsafe_5618_; 
v_exportUnsafe_5618_ = lean_ctor_get_uint8(v_a_4767_, sizeof(void*)*6 + 1);
if (v_exportUnsafe_5618_ == 0)
{
v___y_5616_ = v___x_5617_;
goto v___jp_5615_;
}
else
{
goto v___jp_4878_;
}
}
v___jp_4878_:
{
lean_object* v_visitedNames_4879_; lean_object* v_visitedLevels_4880_; lean_object* v_visitedExprs_4881_; lean_object* v_visitedConstants_4882_; lean_object* v_noMDataExprs_4883_; uint8_t v_exportMData_4884_; uint8_t v_exportUnsafe_4885_; uint8_t v_ignoreMissing_4886_; lean_object* v_recursorMap_4887_; uint8_t v___x_4888_; 
v_visitedNames_4879_ = lean_ctor_get(v_a_4767_, 0);
v_visitedLevels_4880_ = lean_ctor_get(v_a_4767_, 1);
v_visitedExprs_4881_ = lean_ctor_get(v_a_4767_, 2);
v_visitedConstants_4882_ = lean_ctor_get(v_a_4767_, 3);
v_noMDataExprs_4883_ = lean_ctor_get(v_a_4767_, 4);
v_exportMData_4884_ = lean_ctor_get_uint8(v_a_4767_, sizeof(void*)*6);
v_exportUnsafe_4885_ = lean_ctor_get_uint8(v_a_4767_, sizeof(void*)*6 + 1);
v_ignoreMissing_4886_ = lean_ctor_get_uint8(v_a_4767_, sizeof(void*)*6 + 2);
v_recursorMap_4887_ = lean_ctor_get(v_a_4767_, 5);
v___x_4888_ = l_Lean_NameHashSet_contains(v_visitedConstants_4882_, v_c_4765_);
if (v___x_4888_ == 0)
{
lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_5608_; 
lean_inc(v_recursorMap_4887_);
lean_inc_ref(v_noMDataExprs_4883_);
lean_inc_ref(v_visitedConstants_4882_);
lean_inc_ref(v_visitedExprs_4881_);
lean_inc_ref(v_visitedLevels_4880_);
lean_inc_ref(v_visitedNames_4879_);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_a_4767_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; lean_object* v_unused_5610_; lean_object* v_unused_5611_; lean_object* v_unused_5612_; lean_object* v_unused_5613_; lean_object* v_unused_5614_; 
v_unused_5609_ = lean_ctor_get(v_a_4767_, 5);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_a_4767_, 4);
lean_dec(v_unused_5610_);
v_unused_5611_ = lean_ctor_get(v_a_4767_, 3);
lean_dec(v_unused_5611_);
v_unused_5612_ = lean_ctor_get(v_a_4767_, 2);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_a_4767_, 1);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_a_4767_, 0);
lean_dec(v_unused_5614_);
v___x_4890_ = v_a_4767_;
v_isShared_4891_ = v_isSharedCheck_5608_;
goto v_resetjp_4889_;
}
else
{
lean_dec(v_a_4767_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_5608_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4894_; 
v___x_4892_ = l_Lean_NameHashSet_insert(v_visitedConstants_4882_, v_c_4765_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 3, v___x_4892_);
v___x_4894_ = v___x_4890_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_visitedNames_4879_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v_visitedLevels_4880_);
lean_ctor_set(v_reuseFailAlloc_5607_, 2, v_visitedExprs_4881_);
lean_ctor_set(v_reuseFailAlloc_5607_, 3, v___x_4892_);
lean_ctor_set(v_reuseFailAlloc_5607_, 4, v_noMDataExprs_4883_);
lean_ctor_set(v_reuseFailAlloc_5607_, 5, v_recursorMap_4887_);
lean_ctor_set_uint8(v_reuseFailAlloc_5607_, sizeof(void*)*6, v_exportMData_4884_);
lean_ctor_set_uint8(v_reuseFailAlloc_5607_, sizeof(void*)*6 + 1, v_exportUnsafe_4885_);
lean_ctor_set_uint8(v_reuseFailAlloc_5607_, sizeof(void*)*6 + 2, v_ignoreMissing_4886_);
v___x_4894_ = v_reuseFailAlloc_5607_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
switch(lean_obj_tag(v_val_4877_))
{
case 0:
{
lean_object* v_val_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4999_; 
v_val_4895_ = lean_ctor_get(v_val_4877_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_val_4877_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4897_ = v_val_4877_;
v_isShared_4898_ = v_isSharedCheck_4999_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_val_4895_);
lean_dec(v_val_4877_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4999_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v_toConstantVal_4899_; uint8_t v_isUnsafe_4900_; lean_object* v_name_4901_; lean_object* v_levelParams_4902_; lean_object* v_type_4903_; lean_object* v___x_4904_; 
v_toConstantVal_4899_ = lean_ctor_get(v_val_4895_, 0);
lean_inc_ref(v_toConstantVal_4899_);
v_isUnsafe_4900_ = lean_ctor_get_uint8(v_val_4895_, sizeof(void*)*1);
lean_dec_ref(v_val_4895_);
v_name_4901_ = lean_ctor_get(v_toConstantVal_4899_, 0);
lean_inc(v_name_4901_);
v_levelParams_4902_ = lean_ctor_get(v_toConstantVal_4899_, 1);
lean_inc(v_levelParams_4902_);
v_type_4903_ = lean_ctor_get(v_toConstantVal_4899_, 2);
lean_inc_ref_n(v_type_4903_, 2);
lean_dec_ref(v_toConstantVal_4899_);
v___x_4904_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_4903_, v_a_4766_, v___x_4894_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4998_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4907_ = v___x_4904_;
v_isShared_4908_ = v_isSharedCheck_4998_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4998_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_snd_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4996_; 
v_snd_4909_ = lean_ctor_get(v_a_4905_, 1);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_a_4905_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v_a_4905_, 0);
lean_dec(v_unused_4997_);
v___x_4911_ = v_a_4905_;
v_isShared_4912_ = v_isSharedCheck_4996_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_snd_4909_);
lean_dec(v_a_4905_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4996_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4913_; 
v___x_4913_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_4901_, v_a_4766_, v_snd_4909_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; lean_object* v_fst_4915_; lean_object* v_snd_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4987_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc(v_a_4914_);
lean_dec_ref_known(v___x_4913_, 1);
v_fst_4915_ = lean_ctor_get(v_a_4914_, 0);
v_snd_4916_ = lean_ctor_get(v_a_4914_, 1);
v_isSharedCheck_4987_ = !lean_is_exclusive(v_a_4914_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4918_ = v_a_4914_;
v_isShared_4919_ = v_isSharedCheck_4987_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_snd_4916_);
lean_inc(v_fst_4915_);
lean_dec(v_a_4914_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4987_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4920_; 
v___x_4920_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_4902_, v_a_4766_, v_snd_4916_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v_fst_4922_; lean_object* v_snd_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4978_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4920_, 1);
v_fst_4922_ = lean_ctor_get(v_a_4921_, 0);
v_snd_4923_ = lean_ctor_get(v_a_4921_, 1);
v_isSharedCheck_4978_ = !lean_is_exclusive(v_a_4921_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4925_ = v_a_4921_;
v_isShared_4926_ = v_isSharedCheck_4978_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_snd_4923_);
lean_inc(v_fst_4922_);
lean_dec(v_a_4921_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4978_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4927_; 
v___x_4927_ = l_LeanExport_dumpExpr(v_type_4903_, v_a_4766_, v_snd_4923_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v_fst_4929_; lean_object* v_snd_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4969_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___x_4927_, 1);
v_fst_4929_ = lean_ctor_get(v_a_4928_, 0);
v_snd_4930_ = lean_ctor_get(v_a_4928_, 1);
v_isSharedCheck_4969_ = !lean_is_exclusive(v_a_4928_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4932_ = v_a_4928_;
v_isShared_4933_ = v_isSharedCheck_4969_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_snd_4930_);
lean_inc(v_fst_4929_);
lean_dec(v_a_4928_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4969_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4938_; 
v___x_4934_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__3));
v___x_4935_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_4936_ = l_Lean_JsonNumber_fromNat(v_fst_4915_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set_tag(v___x_4907_, 2);
lean_ctor_set(v___x_4907_, 0, v___x_4936_);
v___x_4938_ = v___x_4907_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4936_);
v___x_4938_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4940_; 
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 1, v___x_4938_);
lean_ctor_set(v___x_4932_, 0, v___x_4935_);
v___x_4940_ = v___x_4932_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4967_, 1, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
lean_object* v___x_4941_; lean_object* v___x_4943_; 
v___x_4941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 1, v_fst_4922_);
lean_ctor_set(v___x_4925_, 0, v___x_4941_);
v___x_4943_ = v___x_4925_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4941_);
lean_ctor_set(v_reuseFailAlloc_4966_, 1, v_fst_4922_);
v___x_4943_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4947_; 
v___x_4944_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_4945_ = l_Lean_JsonNumber_fromNat(v_fst_4929_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set_tag(v___x_4897_, 2);
lean_ctor_set(v___x_4897_, 0, v___x_4945_);
v___x_4947_ = v___x_4897_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4945_);
v___x_4947_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
lean_object* v___x_4949_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 1, v___x_4947_);
lean_ctor_set(v___x_4918_, 0, v___x_4944_);
v___x_4949_ = v___x_4918_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4944_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_4951_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4951_, 0, v_isUnsafe_4900_);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 1, v___x_4951_);
lean_ctor_set(v___x_4911_, 0, v___x_4950_);
v___x_4953_ = v___x_4911_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4950_);
lean_ctor_set(v_reuseFailAlloc_4963_, 1, v___x_4951_);
v___x_4953_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4954_ = lean_box(0);
v___x_4955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4953_);
lean_ctor_set(v___x_4955_, 1, v___x_4954_);
v___x_4956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4949_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
v___x_4957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4943_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4940_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = l_Lean_Json_mkObj(v___x_4958_);
lean_dec_ref_known(v___x_4958_, 2);
v___x_4960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4934_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
lean_ctor_set(v___x_4961_, 1, v___x_4954_);
v___x_4962_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4961_, v_snd_4930_);
lean_dec_ref_known(v___x_4961_, 2);
return v___x_4962_;
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
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_del_object(v___x_4925_);
lean_dec(v_fst_4922_);
lean_del_object(v___x_4918_);
lean_dec(v_fst_4915_);
lean_del_object(v___x_4911_);
lean_del_object(v___x_4907_);
lean_del_object(v___x_4897_);
v_a_4970_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4927_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4927_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
lean_del_object(v___x_4918_);
lean_dec(v_fst_4915_);
lean_del_object(v___x_4911_);
lean_del_object(v___x_4907_);
lean_dec_ref(v_type_4903_);
lean_del_object(v___x_4897_);
v_a_4979_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4920_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4920_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_del_object(v___x_4911_);
lean_del_object(v___x_4907_);
lean_dec_ref(v_type_4903_);
lean_dec(v_levelParams_4902_);
lean_del_object(v___x_4897_);
v_a_4988_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4913_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4913_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_type_4903_);
lean_dec(v_levelParams_4902_);
lean_dec(v_name_4901_);
lean_del_object(v___x_4897_);
return v___x_4904_;
}
}
}
case 1:
{
lean_object* v_val_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5171_; 
v_val_5000_ = lean_ctor_get(v_val_4877_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v_val_4877_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5002_ = v_val_4877_;
v_isShared_5003_ = v_isSharedCheck_5171_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_val_5000_);
lean_dec(v_val_4877_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5171_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v_toConstantVal_5004_; lean_object* v_value_5005_; lean_object* v_hints_5006_; uint8_t v_safety_5007_; lean_object* v_all_5008_; lean_object* v_name_5009_; lean_object* v_levelParams_5010_; lean_object* v_type_5011_; lean_object* v___x_5012_; 
v_toConstantVal_5004_ = lean_ctor_get(v_val_5000_, 0);
lean_inc_ref(v_toConstantVal_5004_);
v_value_5005_ = lean_ctor_get(v_val_5000_, 1);
lean_inc_ref(v_value_5005_);
v_hints_5006_ = lean_ctor_get(v_val_5000_, 2);
lean_inc(v_hints_5006_);
v_safety_5007_ = lean_ctor_get_uint8(v_val_5000_, sizeof(void*)*4);
v_all_5008_ = lean_ctor_get(v_val_5000_, 3);
lean_inc(v_all_5008_);
lean_dec_ref(v_val_5000_);
v_name_5009_ = lean_ctor_get(v_toConstantVal_5004_, 0);
lean_inc(v_name_5009_);
v_levelParams_5010_ = lean_ctor_get(v_toConstantVal_5004_, 1);
lean_inc(v_levelParams_5010_);
v_type_5011_ = lean_ctor_get(v_toConstantVal_5004_, 2);
lean_inc_ref_n(v_type_5011_, 2);
lean_dec_ref(v_toConstantVal_5004_);
v___x_5012_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5011_, v_a_4766_, v___x_4894_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5170_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5015_ = v___x_5012_;
v_isShared_5016_ = v_isSharedCheck_5170_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_5012_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5170_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v_snd_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5168_; 
v_snd_5017_ = lean_ctor_get(v_a_5013_, 1);
v_isSharedCheck_5168_ = !lean_is_exclusive(v_a_5013_);
if (v_isSharedCheck_5168_ == 0)
{
lean_object* v_unused_5169_; 
v_unused_5169_ = lean_ctor_get(v_a_5013_, 0);
lean_dec(v_unused_5169_);
v___x_5019_ = v_a_5013_;
v_isShared_5020_ = v_isSharedCheck_5168_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_snd_5017_);
lean_dec(v_a_5013_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5168_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5021_; 
lean_inc_ref(v_value_5005_);
v___x_5021_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5005_, v_a_4766_, v_snd_5017_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5167_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5024_ = v___x_5021_;
v_isShared_5025_ = v_isSharedCheck_5167_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5167_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v_snd_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5165_; 
v_snd_5026_ = lean_ctor_get(v_a_5022_, 1);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_a_5022_);
if (v_isSharedCheck_5165_ == 0)
{
lean_object* v_unused_5166_; 
v_unused_5166_ = lean_ctor_get(v_a_5022_, 0);
lean_dec(v_unused_5166_);
v___x_5028_ = v_a_5022_;
v_isShared_5029_ = v_isSharedCheck_5165_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_snd_5026_);
lean_dec(v_a_5022_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5165_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5030_; 
v___x_5030_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5009_, v_a_4766_, v_snd_5026_);
if (lean_obj_tag(v___x_5030_) == 0)
{
lean_object* v_a_5031_; lean_object* v_fst_5032_; lean_object* v_snd_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5156_; 
v_a_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_a_5031_);
lean_dec_ref_known(v___x_5030_, 1);
v_fst_5032_ = lean_ctor_get(v_a_5031_, 0);
v_snd_5033_ = lean_ctor_get(v_a_5031_, 1);
v_isSharedCheck_5156_ = !lean_is_exclusive(v_a_5031_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5035_ = v_a_5031_;
v_isShared_5036_ = v_isSharedCheck_5156_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_snd_5033_);
lean_inc(v_fst_5032_);
lean_dec(v_a_5031_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5156_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5037_; 
v___x_5037_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5010_, v_a_4766_, v_snd_5033_);
if (lean_obj_tag(v___x_5037_) == 0)
{
lean_object* v_a_5038_; lean_object* v_fst_5039_; lean_object* v_snd_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5147_; 
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_a_5038_);
lean_dec_ref_known(v___x_5037_, 1);
v_fst_5039_ = lean_ctor_get(v_a_5038_, 0);
v_snd_5040_ = lean_ctor_get(v_a_5038_, 1);
v_isSharedCheck_5147_ = !lean_is_exclusive(v_a_5038_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5042_ = v_a_5038_;
v_isShared_5043_ = v_isSharedCheck_5147_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_snd_5040_);
lean_inc(v_fst_5039_);
lean_dec(v_a_5038_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5147_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5044_; 
v___x_5044_ = l_LeanExport_dumpExpr(v_type_5011_, v_a_4766_, v_snd_5040_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v_fst_5046_; lean_object* v_snd_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5138_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___x_5044_, 1);
v_fst_5046_ = lean_ctor_get(v_a_5045_, 0);
v_snd_5047_ = lean_ctor_get(v_a_5045_, 1);
v_isSharedCheck_5138_ = !lean_is_exclusive(v_a_5045_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5049_ = v_a_5045_;
v_isShared_5050_ = v_isSharedCheck_5138_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_snd_5047_);
lean_inc(v_fst_5046_);
lean_dec(v_a_5045_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5138_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5051_; 
v___x_5051_ = l_LeanExport_dumpExpr(v_value_5005_, v_a_4766_, v_snd_5047_);
if (lean_obj_tag(v___x_5051_) == 0)
{
lean_object* v_a_5052_; lean_object* v_fst_5053_; lean_object* v_snd_5054_; lean_object* v___x_5056_; uint8_t v_isShared_5057_; uint8_t v_isSharedCheck_5129_; 
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc(v_a_5052_);
lean_dec_ref_known(v___x_5051_, 1);
v_fst_5053_ = lean_ctor_get(v_a_5052_, 0);
v_snd_5054_ = lean_ctor_get(v_a_5052_, 1);
v_isSharedCheck_5129_ = !lean_is_exclusive(v_a_5052_);
if (v_isSharedCheck_5129_ == 0)
{
v___x_5056_ = v_a_5052_;
v_isShared_5057_ = v_isSharedCheck_5129_;
goto v_resetjp_5055_;
}
else
{
lean_inc(v_snd_5054_);
lean_inc(v_fst_5053_);
lean_dec(v_a_5052_);
v___x_5056_ = lean_box(0);
v_isShared_5057_ = v_isSharedCheck_5129_;
goto v_resetjp_5055_;
}
v_resetjp_5055_:
{
lean_object* v___x_5058_; 
v___x_5058_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5008_, v_a_4766_, v_snd_5054_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v_a_5059_; lean_object* v_fst_5060_; lean_object* v_snd_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5120_; 
v_a_5059_ = lean_ctor_get(v___x_5058_, 0);
lean_inc(v_a_5059_);
lean_dec_ref_known(v___x_5058_, 1);
v_fst_5060_ = lean_ctor_get(v_a_5059_, 0);
v_snd_5061_ = lean_ctor_get(v_a_5059_, 1);
v_isSharedCheck_5120_ = !lean_is_exclusive(v_a_5059_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5063_ = v_a_5059_;
v_isShared_5064_ = v_isSharedCheck_5120_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_snd_5061_);
lean_inc(v_fst_5060_);
lean_dec(v_a_5059_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5120_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5065_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__4));
v___x_5066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5067_ = l_Lean_JsonNumber_fromNat(v_fst_5032_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 2);
lean_ctor_set(v___x_5024_, 0, v___x_5067_);
v___x_5069_ = v___x_5024_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5071_; 
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 1, v___x_5069_);
lean_ctor_set(v___x_5063_, 0, v___x_5066_);
v___x_5071_ = v___x_5063_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5066_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v___x_5069_);
v___x_5071_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
lean_object* v___x_5072_; lean_object* v___x_5074_; 
v___x_5072_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5057_ == 0)
{
lean_ctor_set(v___x_5056_, 1, v_fst_5039_);
lean_ctor_set(v___x_5056_, 0, v___x_5072_);
v___x_5074_ = v___x_5056_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5072_);
lean_ctor_set(v_reuseFailAlloc_5117_, 1, v_fst_5039_);
v___x_5074_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5078_; 
v___x_5075_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5076_ = l_Lean_JsonNumber_fromNat(v_fst_5046_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set_tag(v___x_5015_, 2);
lean_ctor_set(v___x_5015_, 0, v___x_5076_);
v___x_5078_ = v___x_5015_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5076_);
v___x_5078_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; 
if (v_isShared_5050_ == 0)
{
lean_ctor_set(v___x_5049_, 1, v___x_5078_);
lean_ctor_set(v___x_5049_, 0, v___x_5075_);
v___x_5080_ = v___x_5049_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5075_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; 
v___x_5081_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5082_ = l_Lean_JsonNumber_fromNat(v_fst_5053_);
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 2);
lean_ctor_set(v___x_5002_, 0, v___x_5082_);
v___x_5084_ = v___x_5002_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
lean_object* v___x_5086_; 
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 1, v___x_5084_);
lean_ctor_set(v___x_5042_, 0, v___x_5081_);
v___x_5086_ = v___x_5042_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5081_);
lean_ctor_set(v_reuseFailAlloc_5113_, 1, v___x_5084_);
v___x_5086_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5090_; 
v___x_5087_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__5));
v___x_5088_ = l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson(v_hints_5006_);
lean_dec(v_hints_5006_);
if (v_isShared_5036_ == 0)
{
lean_ctor_set(v___x_5035_, 1, v___x_5088_);
lean_ctor_set(v___x_5035_, 0, v___x_5087_);
v___x_5090_ = v___x_5035_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v___x_5087_);
lean_ctor_set(v_reuseFailAlloc_5112_, 1, v___x_5088_);
v___x_5090_ = v_reuseFailAlloc_5112_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5094_; 
v___x_5091_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__6));
v___x_5092_ = l___private_LeanExport_Basic_0__Lean_DefinitionSafety_toJson(v_safety_5007_);
if (v_isShared_5029_ == 0)
{
lean_ctor_set(v___x_5028_, 1, v___x_5092_);
lean_ctor_set(v___x_5028_, 0, v___x_5091_);
v___x_5094_ = v___x_5028_;
goto v_reusejp_5093_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5091_);
lean_ctor_set(v_reuseFailAlloc_5111_, 1, v___x_5092_);
v___x_5094_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5093_;
}
v_reusejp_5093_:
{
lean_object* v___x_5095_; lean_object* v___x_5097_; 
v___x_5095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5020_ == 0)
{
lean_ctor_set(v___x_5019_, 1, v_fst_5060_);
lean_ctor_set(v___x_5019_, 0, v___x_5095_);
v___x_5097_ = v___x_5019_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v___x_5095_);
lean_ctor_set(v_reuseFailAlloc_5110_, 1, v_fst_5060_);
v___x_5097_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5098_ = lean_box(0);
v___x_5099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5097_);
lean_ctor_set(v___x_5099_, 1, v___x_5098_);
v___x_5100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5094_);
lean_ctor_set(v___x_5100_, 1, v___x_5099_);
v___x_5101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5090_);
lean_ctor_set(v___x_5101_, 1, v___x_5100_);
v___x_5102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5086_);
lean_ctor_set(v___x_5102_, 1, v___x_5101_);
v___x_5103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5080_);
lean_ctor_set(v___x_5103_, 1, v___x_5102_);
v___x_5104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5074_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5071_);
lean_ctor_set(v___x_5105_, 1, v___x_5104_);
v___x_5106_ = l_Lean_Json_mkObj(v___x_5105_);
lean_dec_ref_known(v___x_5105_, 2);
v___x_5107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5065_);
lean_ctor_set(v___x_5107_, 1, v___x_5106_);
v___x_5108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
lean_ctor_set(v___x_5108_, 1, v___x_5098_);
v___x_5109_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5108_, v_snd_5061_);
lean_dec_ref_known(v___x_5108_, 2);
return v___x_5109_;
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
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_del_object(v___x_5056_);
lean_dec(v_fst_5053_);
lean_del_object(v___x_5049_);
lean_dec(v_fst_5046_);
lean_del_object(v___x_5042_);
lean_dec(v_fst_5039_);
lean_del_object(v___x_5035_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec(v_hints_5006_);
lean_del_object(v___x_5002_);
v_a_5121_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5058_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5058_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
}
else
{
lean_object* v_a_5130_; lean_object* v___x_5132_; uint8_t v_isShared_5133_; uint8_t v_isSharedCheck_5137_; 
lean_del_object(v___x_5049_);
lean_dec(v_fst_5046_);
lean_del_object(v___x_5042_);
lean_dec(v_fst_5039_);
lean_del_object(v___x_5035_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_del_object(v___x_5002_);
v_a_5130_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5132_ = v___x_5051_;
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
else
{
lean_inc(v_a_5130_);
lean_dec(v___x_5051_);
v___x_5132_ = lean_box(0);
v_isShared_5133_ = v_isSharedCheck_5137_;
goto v_resetjp_5131_;
}
v_resetjp_5131_:
{
lean_object* v___x_5135_; 
if (v_isShared_5133_ == 0)
{
v___x_5135_ = v___x_5132_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_a_5130_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_del_object(v___x_5042_);
lean_dec(v_fst_5039_);
lean_del_object(v___x_5035_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_dec_ref(v_value_5005_);
lean_del_object(v___x_5002_);
v_a_5139_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_5044_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_5044_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
}
}
else
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5155_; 
lean_del_object(v___x_5035_);
lean_dec(v_fst_5032_);
lean_del_object(v___x_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec_ref(v_type_5011_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_dec_ref(v_value_5005_);
lean_del_object(v___x_5002_);
v_a_5148_ = lean_ctor_get(v___x_5037_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5037_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5150_ = v___x_5037_;
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5037_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5155_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v___x_5153_; 
if (v_isShared_5151_ == 0)
{
v___x_5153_ = v___x_5150_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v_a_5148_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_del_object(v___x_5028_);
lean_del_object(v___x_5024_);
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec_ref(v_type_5011_);
lean_dec(v_levelParams_5010_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_dec_ref(v_value_5005_);
lean_del_object(v___x_5002_);
v_a_5157_ = lean_ctor_get(v___x_5030_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5030_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5030_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5030_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5019_);
lean_del_object(v___x_5015_);
lean_dec_ref(v_type_5011_);
lean_dec(v_levelParams_5010_);
lean_dec(v_name_5009_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_dec_ref(v_value_5005_);
lean_del_object(v___x_5002_);
return v___x_5021_;
}
}
}
}
else
{
lean_dec_ref(v_type_5011_);
lean_dec(v_levelParams_5010_);
lean_dec(v_name_5009_);
lean_dec(v_all_5008_);
lean_dec(v_hints_5006_);
lean_dec_ref(v_value_5005_);
lean_del_object(v___x_5002_);
return v___x_5012_;
}
}
}
case 2:
{
lean_object* v_val_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5333_; 
v_val_5172_ = lean_ctor_get(v_val_4877_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v_val_4877_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5174_ = v_val_4877_;
v_isShared_5175_ = v_isSharedCheck_5333_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_val_5172_);
lean_dec(v_val_4877_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5333_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v_toConstantVal_5176_; lean_object* v_value_5177_; lean_object* v_all_5178_; lean_object* v_name_5179_; lean_object* v_levelParams_5180_; lean_object* v_type_5181_; lean_object* v___x_5182_; 
v_toConstantVal_5176_ = lean_ctor_get(v_val_5172_, 0);
lean_inc_ref(v_toConstantVal_5176_);
v_value_5177_ = lean_ctor_get(v_val_5172_, 1);
lean_inc_ref(v_value_5177_);
v_all_5178_ = lean_ctor_get(v_val_5172_, 2);
lean_inc(v_all_5178_);
lean_dec_ref(v_val_5172_);
v_name_5179_ = lean_ctor_get(v_toConstantVal_5176_, 0);
lean_inc(v_name_5179_);
v_levelParams_5180_ = lean_ctor_get(v_toConstantVal_5176_, 1);
lean_inc(v_levelParams_5180_);
v_type_5181_ = lean_ctor_get(v_toConstantVal_5176_, 2);
lean_inc_ref_n(v_type_5181_, 2);
lean_dec_ref(v_toConstantVal_5176_);
v___x_5182_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5181_, v_a_4766_, v___x_4894_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5332_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5185_ = v___x_5182_;
v_isShared_5186_ = v_isSharedCheck_5332_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5182_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5332_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v_snd_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5330_; 
v_snd_5187_ = lean_ctor_get(v_a_5183_, 1);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_a_5183_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; 
v_unused_5331_ = lean_ctor_get(v_a_5183_, 0);
lean_dec(v_unused_5331_);
v___x_5189_ = v_a_5183_;
v_isShared_5190_ = v_isSharedCheck_5330_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_snd_5187_);
lean_dec(v_a_5183_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5330_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5191_; 
lean_inc_ref(v_value_5177_);
v___x_5191_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5177_, v_a_4766_, v_snd_5187_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5329_; 
v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5194_ = v___x_5191_;
v_isShared_5195_ = v_isSharedCheck_5329_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5191_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5329_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v_snd_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5327_; 
v_snd_5196_ = lean_ctor_get(v_a_5192_, 1);
v_isSharedCheck_5327_ = !lean_is_exclusive(v_a_5192_);
if (v_isSharedCheck_5327_ == 0)
{
lean_object* v_unused_5328_; 
v_unused_5328_ = lean_ctor_get(v_a_5192_, 0);
lean_dec(v_unused_5328_);
v___x_5198_ = v_a_5192_;
v_isShared_5199_ = v_isSharedCheck_5327_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_snd_5196_);
lean_dec(v_a_5192_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5327_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5200_; 
v___x_5200_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5179_, v_a_4766_, v_snd_5196_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; lean_object* v_fst_5202_; lean_object* v_snd_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5318_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v_fst_5202_ = lean_ctor_get(v_a_5201_, 0);
v_snd_5203_ = lean_ctor_get(v_a_5201_, 1);
v_isSharedCheck_5318_ = !lean_is_exclusive(v_a_5201_);
if (v_isSharedCheck_5318_ == 0)
{
v___x_5205_ = v_a_5201_;
v_isShared_5206_ = v_isSharedCheck_5318_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_snd_5203_);
lean_inc(v_fst_5202_);
lean_dec(v_a_5201_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5318_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5207_; 
v___x_5207_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5180_, v_a_4766_, v_snd_5203_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v_fst_5209_; lean_object* v_snd_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5309_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v_fst_5209_ = lean_ctor_get(v_a_5208_, 0);
v_snd_5210_ = lean_ctor_get(v_a_5208_, 1);
v_isSharedCheck_5309_ = !lean_is_exclusive(v_a_5208_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5212_ = v_a_5208_;
v_isShared_5213_ = v_isSharedCheck_5309_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_snd_5210_);
lean_inc(v_fst_5209_);
lean_dec(v_a_5208_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5309_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5214_; 
v___x_5214_ = l_LeanExport_dumpExpr(v_type_5181_, v_a_4766_, v_snd_5210_);
if (lean_obj_tag(v___x_5214_) == 0)
{
lean_object* v_a_5215_; lean_object* v_fst_5216_; lean_object* v_snd_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5300_; 
v_a_5215_ = lean_ctor_get(v___x_5214_, 0);
lean_inc(v_a_5215_);
lean_dec_ref_known(v___x_5214_, 1);
v_fst_5216_ = lean_ctor_get(v_a_5215_, 0);
v_snd_5217_ = lean_ctor_get(v_a_5215_, 1);
v_isSharedCheck_5300_ = !lean_is_exclusive(v_a_5215_);
if (v_isSharedCheck_5300_ == 0)
{
v___x_5219_ = v_a_5215_;
v_isShared_5220_ = v_isSharedCheck_5300_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_snd_5217_);
lean_inc(v_fst_5216_);
lean_dec(v_a_5215_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5300_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5221_; 
v___x_5221_ = l_LeanExport_dumpExpr(v_value_5177_, v_a_4766_, v_snd_5217_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v_fst_5223_; lean_object* v_snd_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5291_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v_fst_5223_ = lean_ctor_get(v_a_5222_, 0);
v_snd_5224_ = lean_ctor_get(v_a_5222_, 1);
v_isSharedCheck_5291_ = !lean_is_exclusive(v_a_5222_);
if (v_isSharedCheck_5291_ == 0)
{
v___x_5226_ = v_a_5222_;
v_isShared_5227_ = v_isSharedCheck_5291_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_snd_5224_);
lean_inc(v_fst_5223_);
lean_dec(v_a_5222_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5291_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v___x_5228_; 
v___x_5228_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5178_, v_a_4766_, v_snd_5224_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v_fst_5230_; lean_object* v_snd_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5282_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
v_fst_5230_ = lean_ctor_get(v_a_5229_, 0);
v_snd_5231_ = lean_ctor_get(v_a_5229_, 1);
v_isSharedCheck_5282_ = !lean_is_exclusive(v_a_5229_);
if (v_isSharedCheck_5282_ == 0)
{
v___x_5233_ = v_a_5229_;
v_isShared_5234_ = v_isSharedCheck_5282_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_snd_5231_);
lean_inc(v_fst_5230_);
lean_dec(v_a_5229_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5282_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5239_; 
v___x_5235_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__7));
v___x_5236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5237_ = l_Lean_JsonNumber_fromNat(v_fst_5202_);
if (v_isShared_5195_ == 0)
{
lean_ctor_set_tag(v___x_5194_, 2);
lean_ctor_set(v___x_5194_, 0, v___x_5237_);
v___x_5239_ = v___x_5194_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5237_);
v___x_5239_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5241_; 
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 1, v___x_5239_);
lean_ctor_set(v___x_5233_, 0, v___x_5236_);
v___x_5241_ = v___x_5233_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v___x_5236_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
lean_object* v___x_5242_; lean_object* v___x_5244_; 
v___x_5242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 1, v_fst_5209_);
lean_ctor_set(v___x_5226_, 0, v___x_5242_);
v___x_5244_ = v___x_5226_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5242_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v_fst_5209_);
v___x_5244_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5248_; 
v___x_5245_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5246_ = l_Lean_JsonNumber_fromNat(v_fst_5216_);
if (v_isShared_5186_ == 0)
{
lean_ctor_set_tag(v___x_5185_, 2);
lean_ctor_set(v___x_5185_, 0, v___x_5246_);
v___x_5248_ = v___x_5185_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5250_; 
if (v_isShared_5220_ == 0)
{
lean_ctor_set(v___x_5219_, 1, v___x_5248_);
lean_ctor_set(v___x_5219_, 0, v___x_5245_);
v___x_5250_ = v___x_5219_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v___x_5245_);
lean_ctor_set(v_reuseFailAlloc_5277_, 1, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5254_; 
v___x_5251_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5252_ = l_Lean_JsonNumber_fromNat(v_fst_5223_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set(v___x_5174_, 0, v___x_5252_);
v___x_5254_ = v___x_5174_;
goto v_reusejp_5253_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5252_);
v___x_5254_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5253_;
}
v_reusejp_5253_:
{
lean_object* v___x_5256_; 
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 1, v___x_5254_);
lean_ctor_set(v___x_5212_, 0, v___x_5251_);
v___x_5256_ = v___x_5212_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5251_);
lean_ctor_set(v_reuseFailAlloc_5275_, 1, v___x_5254_);
v___x_5256_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
lean_object* v___x_5257_; lean_object* v___x_5259_; 
v___x_5257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5206_ == 0)
{
lean_ctor_set(v___x_5205_, 1, v_fst_5230_);
lean_ctor_set(v___x_5205_, 0, v___x_5257_);
v___x_5259_ = v___x_5205_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5257_);
lean_ctor_set(v_reuseFailAlloc_5274_, 1, v_fst_5230_);
v___x_5259_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
lean_object* v___x_5260_; lean_object* v___x_5262_; 
v___x_5260_ = lean_box(0);
if (v_isShared_5190_ == 0)
{
lean_ctor_set_tag(v___x_5189_, 1);
lean_ctor_set(v___x_5189_, 1, v___x_5260_);
lean_ctor_set(v___x_5189_, 0, v___x_5259_);
v___x_5262_ = v___x_5189_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5259_);
lean_ctor_set(v_reuseFailAlloc_5273_, 1, v___x_5260_);
v___x_5262_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5269_; 
v___x_5263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5263_, 0, v___x_5256_);
lean_ctor_set(v___x_5263_, 1, v___x_5262_);
v___x_5264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5250_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
v___x_5265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5265_, 0, v___x_5244_);
lean_ctor_set(v___x_5265_, 1, v___x_5264_);
v___x_5266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5241_);
lean_ctor_set(v___x_5266_, 1, v___x_5265_);
v___x_5267_ = l_Lean_Json_mkObj(v___x_5266_);
lean_dec_ref_known(v___x_5266_, 2);
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 1, v___x_5267_);
lean_ctor_set(v___x_5198_, 0, v___x_5235_);
v___x_5269_ = v___x_5198_;
goto v_reusejp_5268_;
}
else
{
lean_object* v_reuseFailAlloc_5272_; 
v_reuseFailAlloc_5272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5272_, 0, v___x_5235_);
lean_ctor_set(v_reuseFailAlloc_5272_, 1, v___x_5267_);
v___x_5269_ = v_reuseFailAlloc_5272_;
goto v_reusejp_5268_;
}
v_reusejp_5268_:
{
lean_object* v___x_5270_; lean_object* v___x_5271_; 
v___x_5270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5270_, 0, v___x_5269_);
lean_ctor_set(v___x_5270_, 1, v___x_5260_);
v___x_5271_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5270_, v_snd_5231_);
lean_dec_ref_known(v___x_5270_, 2);
return v___x_5271_;
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
}
else
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5290_; 
lean_del_object(v___x_5226_);
lean_dec(v_fst_5223_);
lean_del_object(v___x_5219_);
lean_dec(v_fst_5216_);
lean_del_object(v___x_5212_);
lean_dec(v_fst_5209_);
lean_del_object(v___x_5205_);
lean_dec(v_fst_5202_);
lean_del_object(v___x_5198_);
lean_del_object(v___x_5194_);
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_del_object(v___x_5174_);
v_a_5283_ = lean_ctor_get(v___x_5228_, 0);
v_isSharedCheck_5290_ = !lean_is_exclusive(v___x_5228_);
if (v_isSharedCheck_5290_ == 0)
{
v___x_5285_ = v___x_5228_;
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5228_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5290_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v___x_5288_; 
if (v_isShared_5286_ == 0)
{
v___x_5288_ = v___x_5285_;
goto v_reusejp_5287_;
}
else
{
lean_object* v_reuseFailAlloc_5289_; 
v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_a_5283_);
v___x_5288_ = v_reuseFailAlloc_5289_;
goto v_reusejp_5287_;
}
v_reusejp_5287_:
{
return v___x_5288_;
}
}
}
}
}
else
{
lean_object* v_a_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5299_; 
lean_del_object(v___x_5219_);
lean_dec(v_fst_5216_);
lean_del_object(v___x_5212_);
lean_dec(v_fst_5209_);
lean_del_object(v___x_5205_);
lean_dec(v_fst_5202_);
lean_del_object(v___x_5198_);
lean_del_object(v___x_5194_);
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_dec(v_all_5178_);
lean_del_object(v___x_5174_);
v_a_5292_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5299_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5299_ == 0)
{
v___x_5294_ = v___x_5221_;
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_a_5292_);
lean_dec(v___x_5221_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5299_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v___x_5297_; 
if (v_isShared_5295_ == 0)
{
v___x_5297_ = v___x_5294_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v_a_5292_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
}
}
else
{
lean_object* v_a_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5308_; 
lean_del_object(v___x_5212_);
lean_dec(v_fst_5209_);
lean_del_object(v___x_5205_);
lean_dec(v_fst_5202_);
lean_del_object(v___x_5198_);
lean_del_object(v___x_5194_);
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_dec(v_all_5178_);
lean_dec_ref(v_value_5177_);
lean_del_object(v___x_5174_);
v_a_5301_ = lean_ctor_get(v___x_5214_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5214_);
if (v_isSharedCheck_5308_ == 0)
{
v___x_5303_ = v___x_5214_;
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_a_5301_);
lean_dec(v___x_5214_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5308_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___x_5306_; 
if (v_isShared_5304_ == 0)
{
v___x_5306_ = v___x_5303_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
}
}
else
{
lean_object* v_a_5310_; lean_object* v___x_5312_; uint8_t v_isShared_5313_; uint8_t v_isSharedCheck_5317_; 
lean_del_object(v___x_5205_);
lean_dec(v_fst_5202_);
lean_del_object(v___x_5198_);
lean_del_object(v___x_5194_);
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_dec_ref(v_type_5181_);
lean_dec(v_all_5178_);
lean_dec_ref(v_value_5177_);
lean_del_object(v___x_5174_);
v_a_5310_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5312_ = v___x_5207_;
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
else
{
lean_inc(v_a_5310_);
lean_dec(v___x_5207_);
v___x_5312_ = lean_box(0);
v_isShared_5313_ = v_isSharedCheck_5317_;
goto v_resetjp_5311_;
}
v_resetjp_5311_:
{
lean_object* v___x_5315_; 
if (v_isShared_5313_ == 0)
{
v___x_5315_ = v___x_5312_;
goto v_reusejp_5314_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
v___x_5315_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5314_;
}
v_reusejp_5314_:
{
return v___x_5315_;
}
}
}
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5321_; uint8_t v_isShared_5322_; uint8_t v_isSharedCheck_5326_; 
lean_del_object(v___x_5198_);
lean_del_object(v___x_5194_);
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_dec_ref(v_type_5181_);
lean_dec(v_levelParams_5180_);
lean_dec(v_all_5178_);
lean_dec_ref(v_value_5177_);
lean_del_object(v___x_5174_);
v_a_5319_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5326_ == 0)
{
v___x_5321_ = v___x_5200_;
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
else
{
lean_inc(v_a_5319_);
lean_dec(v___x_5200_);
v___x_5321_ = lean_box(0);
v_isShared_5322_ = v_isSharedCheck_5326_;
goto v_resetjp_5320_;
}
v_resetjp_5320_:
{
lean_object* v___x_5324_; 
if (v_isShared_5322_ == 0)
{
v___x_5324_ = v___x_5321_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5189_);
lean_del_object(v___x_5185_);
lean_dec_ref(v_type_5181_);
lean_dec(v_levelParams_5180_);
lean_dec(v_name_5179_);
lean_dec(v_all_5178_);
lean_dec_ref(v_value_5177_);
lean_del_object(v___x_5174_);
return v___x_5191_;
}
}
}
}
else
{
lean_dec_ref(v_type_5181_);
lean_dec(v_levelParams_5180_);
lean_dec(v_name_5179_);
lean_dec(v_all_5178_);
lean_dec_ref(v_value_5177_);
lean_del_object(v___x_5174_);
return v___x_5182_;
}
}
}
case 3:
{
lean_object* v_val_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5500_; 
v_val_5334_ = lean_ctor_get(v_val_4877_, 0);
v_isSharedCheck_5500_ = !lean_is_exclusive(v_val_4877_);
if (v_isSharedCheck_5500_ == 0)
{
v___x_5336_ = v_val_4877_;
v_isShared_5337_ = v_isSharedCheck_5500_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_val_5334_);
lean_dec(v_val_4877_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5500_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v_toConstantVal_5338_; lean_object* v_value_5339_; uint8_t v_isUnsafe_5340_; lean_object* v_all_5341_; lean_object* v_name_5342_; lean_object* v_levelParams_5343_; lean_object* v_type_5344_; lean_object* v___x_5345_; 
v_toConstantVal_5338_ = lean_ctor_get(v_val_5334_, 0);
lean_inc_ref(v_toConstantVal_5338_);
v_value_5339_ = lean_ctor_get(v_val_5334_, 1);
lean_inc_ref(v_value_5339_);
v_isUnsafe_5340_ = lean_ctor_get_uint8(v_val_5334_, sizeof(void*)*3);
v_all_5341_ = lean_ctor_get(v_val_5334_, 2);
lean_inc(v_all_5341_);
lean_dec_ref(v_val_5334_);
v_name_5342_ = lean_ctor_get(v_toConstantVal_5338_, 0);
lean_inc(v_name_5342_);
v_levelParams_5343_ = lean_ctor_get(v_toConstantVal_5338_, 1);
lean_inc(v_levelParams_5343_);
v_type_5344_ = lean_ctor_get(v_toConstantVal_5338_, 2);
lean_inc_ref_n(v_type_5344_, 2);
lean_dec_ref(v_toConstantVal_5338_);
v___x_5345_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_type_5344_, v_a_4766_, v___x_4894_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5499_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5499_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5499_ == 0)
{
v___x_5348_ = v___x_5345_;
v_isShared_5349_ = v_isSharedCheck_5499_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5345_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5499_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v_snd_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5497_; 
v_snd_5350_ = lean_ctor_get(v_a_5346_, 1);
v_isSharedCheck_5497_ = !lean_is_exclusive(v_a_5346_);
if (v_isSharedCheck_5497_ == 0)
{
lean_object* v_unused_5498_; 
v_unused_5498_ = lean_ctor_get(v_a_5346_, 0);
lean_dec(v_unused_5498_);
v___x_5352_ = v_a_5346_;
v_isShared_5353_ = v_isSharedCheck_5497_;
goto v_resetjp_5351_;
}
else
{
lean_inc(v_snd_5350_);
lean_dec(v_a_5346_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5497_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5354_; 
lean_inc_ref(v_value_5339_);
v___x_5354_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_value_5339_, v_a_4766_, v_snd_5350_);
if (lean_obj_tag(v___x_5354_) == 0)
{
lean_object* v_a_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5496_; 
v_a_5355_ = lean_ctor_get(v___x_5354_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5354_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5357_ = v___x_5354_;
v_isShared_5358_ = v_isSharedCheck_5496_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_a_5355_);
lean_dec(v___x_5354_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5496_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v_snd_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5494_; 
v_snd_5359_ = lean_ctor_get(v_a_5355_, 1);
v_isSharedCheck_5494_ = !lean_is_exclusive(v_a_5355_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; 
v_unused_5495_ = lean_ctor_get(v_a_5355_, 0);
lean_dec(v_unused_5495_);
v___x_5361_ = v_a_5355_;
v_isShared_5362_ = v_isSharedCheck_5494_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_snd_5359_);
lean_dec(v_a_5355_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5494_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v___x_5363_; 
v___x_5363_ = l___private_LeanExport_Basic_0__LeanExport_dumpName(v_name_5342_, v_a_4766_, v_snd_5359_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; lean_object* v_fst_5365_; lean_object* v_snd_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5485_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
lean_dec_ref_known(v___x_5363_, 1);
v_fst_5365_ = lean_ctor_get(v_a_5364_, 0);
v_snd_5366_ = lean_ctor_get(v_a_5364_, 1);
v_isSharedCheck_5485_ = !lean_is_exclusive(v_a_5364_);
if (v_isSharedCheck_5485_ == 0)
{
v___x_5368_ = v_a_5364_;
v_isShared_5369_ = v_isSharedCheck_5485_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_snd_5366_);
lean_inc(v_fst_5365_);
lean_dec(v_a_5364_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5485_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5370_; 
v___x_5370_ = l___private_LeanExport_Basic_0__LeanExport_dumpUparams(v_levelParams_5343_, v_a_4766_, v_snd_5366_);
if (lean_obj_tag(v___x_5370_) == 0)
{
lean_object* v_a_5371_; lean_object* v_fst_5372_; lean_object* v_snd_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5476_; 
v_a_5371_ = lean_ctor_get(v___x_5370_, 0);
lean_inc(v_a_5371_);
lean_dec_ref_known(v___x_5370_, 1);
v_fst_5372_ = lean_ctor_get(v_a_5371_, 0);
v_snd_5373_ = lean_ctor_get(v_a_5371_, 1);
v_isSharedCheck_5476_ = !lean_is_exclusive(v_a_5371_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5375_ = v_a_5371_;
v_isShared_5376_ = v_isSharedCheck_5476_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_snd_5373_);
lean_inc(v_fst_5372_);
lean_dec(v_a_5371_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5476_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5377_; 
v___x_5377_ = l_LeanExport_dumpExpr(v_type_5344_, v_a_4766_, v_snd_5373_);
if (lean_obj_tag(v___x_5377_) == 0)
{
lean_object* v_a_5378_; lean_object* v_fst_5379_; lean_object* v_snd_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5467_; 
v_a_5378_ = lean_ctor_get(v___x_5377_, 0);
lean_inc(v_a_5378_);
lean_dec_ref_known(v___x_5377_, 1);
v_fst_5379_ = lean_ctor_get(v_a_5378_, 0);
v_snd_5380_ = lean_ctor_get(v_a_5378_, 1);
v_isSharedCheck_5467_ = !lean_is_exclusive(v_a_5378_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5382_ = v_a_5378_;
v_isShared_5383_ = v_isSharedCheck_5467_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_snd_5380_);
lean_inc(v_fst_5379_);
lean_dec(v_a_5378_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5467_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v___x_5384_; 
v___x_5384_ = l_LeanExport_dumpExpr(v_value_5339_, v_a_4766_, v_snd_5380_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v_a_5385_; lean_object* v_fst_5386_; lean_object* v_snd_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5458_; 
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
lean_inc(v_a_5385_);
lean_dec_ref_known(v___x_5384_, 1);
v_fst_5386_ = lean_ctor_get(v_a_5385_, 0);
v_snd_5387_ = lean_ctor_get(v_a_5385_, 1);
v_isSharedCheck_5458_ = !lean_is_exclusive(v_a_5385_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5389_ = v_a_5385_;
v_isShared_5390_ = v_isSharedCheck_5458_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_snd_5387_);
lean_inc(v_fst_5386_);
lean_dec(v_a_5385_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5458_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5391_; 
v___x_5391_ = l___private_LeanExport_Basic_0__LeanExport_dumpNames(v_all_5341_, v_a_4766_, v_snd_5387_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; lean_object* v_fst_5393_; lean_object* v_snd_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5449_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
lean_inc(v_a_5392_);
lean_dec_ref_known(v___x_5391_, 1);
v_fst_5393_ = lean_ctor_get(v_a_5392_, 0);
v_snd_5394_ = lean_ctor_get(v_a_5392_, 1);
v_isSharedCheck_5449_ = !lean_is_exclusive(v_a_5392_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5396_ = v_a_5392_;
v_isShared_5397_ = v_isSharedCheck_5449_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_snd_5394_);
lean_inc(v_fst_5393_);
lean_dec(v_a_5392_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5449_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; lean_object* v___x_5402_; 
v___x_5398_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_ReducibilityHints_toJson___closed__0));
v___x_5399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__0));
v___x_5400_ = l_Lean_JsonNumber_fromNat(v_fst_5365_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set_tag(v___x_5357_, 2);
lean_ctor_set(v___x_5357_, 0, v___x_5400_);
v___x_5402_ = v___x_5357_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5400_);
v___x_5402_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
lean_object* v___x_5404_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5402_);
lean_ctor_set(v___x_5396_, 0, v___x_5399_);
v___x_5404_ = v___x_5396_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v___x_5399_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
lean_object* v___x_5405_; lean_object* v___x_5407_; 
v___x_5405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__1));
if (v_isShared_5390_ == 0)
{
lean_ctor_set(v___x_5389_, 1, v_fst_5372_);
lean_ctor_set(v___x_5389_, 0, v___x_5405_);
v___x_5407_ = v___x_5389_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5405_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_fst_5372_);
v___x_5407_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5411_; 
v___x_5408_ = ((lean_object*)(l___private_LeanExport_Basic_0__Lean_QuotKind_toJson___closed__0));
v___x_5409_ = l_Lean_JsonNumber_fromNat(v_fst_5379_);
if (v_isShared_5349_ == 0)
{
lean_ctor_set_tag(v___x_5348_, 2);
lean_ctor_set(v___x_5348_, 0, v___x_5409_);
v___x_5411_ = v___x_5348_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
lean_object* v___x_5413_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5411_);
lean_ctor_set(v___x_5382_, 0, v___x_5408_);
v___x_5413_ = v___x_5382_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5417_; 
v___x_5414_ = ((lean_object*)(l_LeanExport_dumpExprAux___closed__13));
v___x_5415_ = l_Lean_JsonNumber_fromNat(v_fst_5386_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set_tag(v___x_5336_, 2);
lean_ctor_set(v___x_5336_, 0, v___x_5415_);
v___x_5417_ = v___x_5336_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5415_);
v___x_5417_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5419_; 
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 1, v___x_5417_);
lean_ctor_set(v___x_5375_, 0, v___x_5414_);
v___x_5419_ = v___x_5375_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v___x_5414_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v___x_5417_);
v___x_5419_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
lean_object* v___x_5420_; lean_object* v___x_5422_; 
v___x_5420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__1));
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v_fst_5393_);
lean_ctor_set(v___x_5368_, 0, v___x_5420_);
v___x_5422_ = v___x_5368_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5420_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v_fst_5393_);
v___x_5422_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5426_; 
v___x_5423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___closed__6));
v___x_5424_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_5424_, 0, v_isUnsafe_5340_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5424_);
lean_ctor_set(v___x_5361_, 0, v___x_5423_);
v___x_5426_ = v___x_5361_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v___x_5423_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; lean_object* v___x_5436_; 
v___x_5427_ = lean_box(0);
v___x_5428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5426_);
lean_ctor_set(v___x_5428_, 1, v___x_5427_);
v___x_5429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5422_);
lean_ctor_set(v___x_5429_, 1, v___x_5428_);
v___x_5430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5419_);
lean_ctor_set(v___x_5430_, 1, v___x_5429_);
v___x_5431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5413_);
lean_ctor_set(v___x_5431_, 1, v___x_5430_);
v___x_5432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5407_);
lean_ctor_set(v___x_5432_, 1, v___x_5431_);
v___x_5433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5404_);
lean_ctor_set(v___x_5433_, 1, v___x_5432_);
v___x_5434_ = l_Lean_Json_mkObj(v___x_5433_);
lean_dec_ref_known(v___x_5433_, 2);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 1, v___x_5434_);
lean_ctor_set(v___x_5352_, 0, v___x_5398_);
v___x_5436_ = v___x_5352_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v___x_5398_);
lean_ctor_set(v_reuseFailAlloc_5439_, 1, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5436_);
lean_ctor_set(v___x_5437_, 1, v___x_5427_);
v___x_5438_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_5437_, v_snd_5394_);
lean_dec_ref_known(v___x_5437_, 2);
return v___x_5438_;
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
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5382_);
lean_dec(v_fst_5379_);
lean_del_object(v___x_5375_);
lean_dec(v_fst_5372_);
lean_del_object(v___x_5368_);
lean_dec(v_fst_5365_);
lean_del_object(v___x_5361_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_del_object(v___x_5336_);
v_a_5450_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5391_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5391_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_del_object(v___x_5382_);
lean_dec(v_fst_5379_);
lean_del_object(v___x_5375_);
lean_dec(v_fst_5372_);
lean_del_object(v___x_5368_);
lean_dec(v_fst_5365_);
lean_del_object(v___x_5361_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_dec(v_all_5341_);
lean_del_object(v___x_5336_);
v_a_5459_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5384_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5384_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_del_object(v___x_5375_);
lean_dec(v_fst_5372_);
lean_del_object(v___x_5368_);
lean_dec(v_fst_5365_);
lean_del_object(v___x_5361_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_dec(v_all_5341_);
lean_dec_ref(v_value_5339_);
lean_del_object(v___x_5336_);
v_a_5468_ = lean_ctor_get(v___x_5377_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5377_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5377_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5377_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
}
else
{
lean_object* v_a_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5484_; 
lean_del_object(v___x_5368_);
lean_dec(v_fst_5365_);
lean_del_object(v___x_5361_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_dec_ref(v_type_5344_);
lean_dec(v_all_5341_);
lean_dec_ref(v_value_5339_);
lean_del_object(v___x_5336_);
v_a_5477_ = lean_ctor_get(v___x_5370_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5479_ = v___x_5370_;
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_a_5477_);
lean_dec(v___x_5370_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5482_; 
if (v_isShared_5480_ == 0)
{
v___x_5482_ = v___x_5479_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
return v___x_5482_;
}
}
}
}
}
else
{
lean_object* v_a_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5493_; 
lean_del_object(v___x_5361_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_dec_ref(v_type_5344_);
lean_dec(v_levelParams_5343_);
lean_dec(v_all_5341_);
lean_dec_ref(v_value_5339_);
lean_del_object(v___x_5336_);
v_a_5486_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5488_ = v___x_5363_;
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
else
{
lean_inc(v_a_5486_);
lean_dec(v___x_5363_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5493_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5491_; 
if (v_isShared_5489_ == 0)
{
v___x_5491_ = v___x_5488_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_5352_);
lean_del_object(v___x_5348_);
lean_dec_ref(v_type_5344_);
lean_dec(v_levelParams_5343_);
lean_dec(v_name_5342_);
lean_dec(v_all_5341_);
lean_dec_ref(v_value_5339_);
lean_del_object(v___x_5336_);
return v___x_5354_;
}
}
}
}
else
{
lean_dec_ref(v_type_5344_);
lean_dec(v_levelParams_5343_);
lean_dec(v_name_5342_);
lean_dec(v_all_5341_);
lean_dec_ref(v_value_5339_);
lean_del_object(v___x_5336_);
return v___x_5345_;
}
}
}
case 4:
{
lean_object* v___x_5501_; lean_object* v___x_5502_; 
lean_dec_ref_known(v_val_4877_, 1);
v___x_5501_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__9));
v___x_5502_ = l_LeanExport_dumpConstant(v___x_5501_, v_a_4766_, v___x_4894_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v_snd_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_a_5503_);
lean_dec_ref_known(v___x_5502_, 1);
v_snd_5504_ = lean_ctor_get(v_a_5503_, 1);
lean_inc(v_snd_5504_);
lean_dec(v_a_5503_);
v___x_5505_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__19));
v___x_5506_ = lean_box(0);
v___x_5507_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__0));
v___x_5508_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_4888_, v___x_5505_, v___x_5507_, v_a_4766_, v_snd_5504_);
if (lean_obj_tag(v___x_5508_) == 0)
{
lean_object* v_a_5509_; lean_object* v___x_5511_; uint8_t v_isShared_5512_; uint8_t v_isSharedCheck_5535_; 
v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5511_ = v___x_5508_;
v_isShared_5512_ = v_isSharedCheck_5535_;
goto v_resetjp_5510_;
}
else
{
lean_inc(v_a_5509_);
lean_dec(v___x_5508_);
v___x_5511_ = lean_box(0);
v_isShared_5512_ = v_isSharedCheck_5535_;
goto v_resetjp_5510_;
}
v_resetjp_5510_:
{
lean_object* v_fst_5513_; lean_object* v_fst_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5533_; 
v_fst_5513_ = lean_ctor_get(v_a_5509_, 0);
lean_inc(v_fst_5513_);
v_fst_5514_ = lean_ctor_get(v_fst_5513_, 0);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_fst_5513_);
if (v_isSharedCheck_5533_ == 0)
{
lean_object* v_unused_5534_; 
v_unused_5534_ = lean_ctor_get(v_fst_5513_, 1);
lean_dec(v_unused_5534_);
v___x_5516_ = v_fst_5513_;
v_isShared_5517_ = v_isSharedCheck_5533_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_fst_5514_);
lean_dec(v_fst_5513_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5533_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
if (lean_obj_tag(v_fst_5514_) == 0)
{
lean_object* v_snd_5518_; lean_object* v___x_5520_; 
v_snd_5518_ = lean_ctor_get(v_a_5509_, 1);
lean_inc(v_snd_5518_);
lean_dec(v_a_5509_);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v_snd_5518_);
lean_ctor_set(v___x_5516_, 0, v___x_5506_);
v___x_5520_ = v___x_5516_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5506_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_snd_5518_);
v___x_5520_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
lean_object* v___x_5522_; 
if (v_isShared_5512_ == 0)
{
lean_ctor_set(v___x_5511_, 0, v___x_5520_);
v___x_5522_ = v___x_5511_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
else
{
lean_object* v_snd_5525_; lean_object* v_val_5526_; lean_object* v___x_5528_; 
v_snd_5525_ = lean_ctor_get(v_a_5509_, 1);
lean_inc(v_snd_5525_);
lean_dec(v_a_5509_);
v_val_5526_ = lean_ctor_get(v_fst_5514_, 0);
lean_inc(v_val_5526_);
lean_dec_ref_known(v_fst_5514_, 1);
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 1, v_snd_5525_);
lean_ctor_set(v___x_5516_, 0, v_val_5526_);
v___x_5528_ = v___x_5516_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_val_5526_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v_snd_5525_);
v___x_5528_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
lean_object* v___x_5530_; 
if (v_isShared_5512_ == 0)
{
lean_ctor_set(v___x_5511_, 0, v___x_5528_);
v___x_5530_ = v___x_5511_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5528_);
v___x_5530_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
return v___x_5530_;
}
}
}
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
v_a_5536_ = lean_ctor_get(v___x_5508_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5508_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5508_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
else
{
return v___x_5502_;
}
}
case 5:
{
lean_object* v_val_5544_; lean_object* v_all_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; 
v_val_5544_ = lean_ctor_get(v_val_4877_, 0);
lean_inc_ref(v_val_5544_);
lean_dec_ref_known(v_val_4877_, 1);
v_all_5545_ = lean_ctor_get(v_val_5544_, 3);
lean_inc(v_all_5545_);
v___x_5546_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__20));
v___x_5547_ = lean_obj_once(&l_LeanExport_dumpConstant___closed__22, &l_LeanExport_dumpConstant___closed__22_once, _init_l_LeanExport_dumpConstant___closed__22);
v___x_5548_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_4888_, v_val_5544_, v_all_5545_, v___x_5547_, v_a_4766_, v___x_4894_);
lean_dec(v_all_5545_);
lean_dec_ref(v_val_5544_);
if (lean_obj_tag(v___x_5548_) == 0)
{
lean_object* v_a_5549_; lean_object* v_fst_5550_; lean_object* v_snd_5551_; lean_object* v_snd_5552_; lean_object* v_fst_5553_; lean_object* v_fst_5554_; lean_object* v_snd_5555_; lean_object* v___x_5556_; size_t v_sz_5557_; size_t v___x_5558_; lean_object* v___x_5559_; 
v_a_5549_ = lean_ctor_get(v___x_5548_, 0);
lean_inc(v_a_5549_);
lean_dec_ref_known(v___x_5548_, 1);
v_fst_5550_ = lean_ctor_get(v_a_5549_, 0);
lean_inc(v_fst_5550_);
v_snd_5551_ = lean_ctor_get(v_fst_5550_, 1);
lean_inc(v_snd_5551_);
v_snd_5552_ = lean_ctor_get(v_a_5549_, 1);
lean_inc(v_snd_5552_);
lean_dec(v_a_5549_);
v_fst_5553_ = lean_ctor_get(v_fst_5550_, 0);
lean_inc(v_fst_5553_);
lean_dec(v_fst_5550_);
v_fst_5554_ = lean_ctor_get(v_snd_5551_, 0);
lean_inc(v_fst_5554_);
v_snd_5555_ = lean_ctor_get(v_snd_5551_, 1);
lean_inc(v_snd_5555_);
lean_dec(v_snd_5551_);
v___x_5556_ = lean_box(0);
v_sz_5557_ = lean_array_size(v_fst_5554_);
v___x_5558_ = ((size_t)0ULL);
v___x_5559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_fst_5554_, v_sz_5557_, v___x_5558_, v___x_5556_, v_a_4766_, v_snd_5552_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v_snd_5561_; lean_object* v___x_5562_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_a_5560_);
lean_dec_ref_known(v___x_5559_, 1);
v_snd_5561_ = lean_ctor_get(v_a_5560_, 1);
lean_inc(v_snd_5561_);
lean_dec(v_a_5560_);
v___x_5562_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00LeanExport_dumpConstant_spec__21(v___x_4888_, v___x_5546_, v_snd_5555_, v_a_4766_, v_snd_5561_);
if (lean_obj_tag(v___x_5562_) == 0)
{
lean_object* v_a_5563_; lean_object* v_fst_5564_; lean_object* v_snd_5565_; lean_object* v_a_5566_; 
v_a_5563_ = lean_ctor_get(v___x_5562_, 0);
lean_inc(v_a_5563_);
lean_dec_ref_known(v___x_5562_, 1);
v_fst_5564_ = lean_ctor_get(v_a_5563_, 0);
lean_inc(v_fst_5564_);
v_snd_5565_ = lean_ctor_get(v_a_5563_, 1);
lean_inc(v_snd_5565_);
lean_dec(v_a_5563_);
v_a_5566_ = lean_ctor_get(v_fst_5564_, 0);
lean_inc(v_a_5566_);
lean_dec(v_fst_5564_);
v___y_4774_ = v___x_5556_;
v___y_4775_ = v_fst_5554_;
v___y_4776_ = v_fst_5553_;
v_fst_4777_ = v_a_5566_;
v_snd_4778_ = v_snd_5565_;
goto v___jp_4773_;
}
else
{
lean_object* v_a_5567_; lean_object* v___x_5569_; uint8_t v_isShared_5570_; uint8_t v_isSharedCheck_5574_; 
lean_dec(v_fst_5554_);
lean_dec(v_fst_5553_);
v_a_5567_ = lean_ctor_get(v___x_5562_, 0);
v_isSharedCheck_5574_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5574_ == 0)
{
v___x_5569_ = v___x_5562_;
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
else
{
lean_inc(v_a_5567_);
lean_dec(v___x_5562_);
v___x_5569_ = lean_box(0);
v_isShared_5570_ = v_isSharedCheck_5574_;
goto v_resetjp_5568_;
}
v_resetjp_5568_:
{
lean_object* v___x_5572_; 
if (v_isShared_5570_ == 0)
{
v___x_5572_ = v___x_5569_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
v___x_5572_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
return v___x_5572_;
}
}
}
}
else
{
lean_dec(v_snd_5555_);
lean_dec(v_fst_5554_);
lean_dec(v_fst_5553_);
return v___x_5559_;
}
}
else
{
lean_object* v_a_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
v_a_5575_ = lean_ctor_get(v___x_5548_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5548_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5577_ = v___x_5548_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_a_5575_);
lean_dec(v___x_5548_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
case 6:
{
lean_object* v_val_5583_; lean_object* v_induct_5584_; 
v_val_5583_ = lean_ctor_get(v_val_4877_, 0);
lean_inc_ref(v_val_5583_);
lean_dec_ref_known(v_val_4877_, 1);
v_induct_5584_ = lean_ctor_get(v_val_5583_, 1);
lean_inc(v_induct_5584_);
lean_dec_ref(v_val_5583_);
v_c_4765_ = v_induct_5584_;
v_a_4767_ = v___x_4894_;
goto _start;
}
default: 
{
lean_object* v_val_5586_; lean_object* v_all_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
v_val_5586_ = lean_ctor_get(v_val_4877_, 0);
lean_inc_ref(v_val_5586_);
lean_dec_ref_known(v_val_4877_, 1);
v_all_5587_ = lean_ctor_get(v_val_5586_, 1);
lean_inc(v_all_5587_);
lean_dec_ref(v_val_5586_);
v___x_5588_ = lean_box(0);
v___x_5589_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_all_5587_, v___x_5588_, v_a_4766_, v___x_4894_);
lean_dec(v_all_5587_);
if (lean_obj_tag(v___x_5589_) == 0)
{
lean_object* v_a_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5606_; 
v_a_5590_ = lean_ctor_get(v___x_5589_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5592_ = v___x_5589_;
v_isShared_5593_ = v_isSharedCheck_5606_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_a_5590_);
lean_dec(v___x_5589_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5606_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v_snd_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5604_; 
v_snd_5594_ = lean_ctor_get(v_a_5590_, 1);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_a_5590_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_a_5590_, 0);
lean_dec(v_unused_5605_);
v___x_5596_ = v_a_5590_;
v_isShared_5597_ = v_isSharedCheck_5604_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_snd_5594_);
lean_dec(v_a_5590_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5604_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v___x_5599_; 
if (v_isShared_5597_ == 0)
{
lean_ctor_set(v___x_5596_, 0, v___x_5588_);
v___x_5599_ = v___x_5596_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_snd_5594_);
v___x_5599_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
lean_object* v___x_5601_; 
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 0, v___x_5599_);
v___x_5601_ = v___x_5592_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5599_);
v___x_5601_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
return v___x_5601_;
}
}
}
}
}
else
{
return v___x_5589_;
}
}
}
}
}
}
else
{
lean_dec(v_val_4877_);
lean_dec(v_c_4765_);
goto v___jp_4769_;
}
}
v___jp_5615_:
{
if (v___y_5616_ == 0)
{
goto v___jp_4878_;
}
else
{
lean_dec(v_val_4877_);
lean_dec(v_c_4765_);
goto v___jp_4769_;
}
}
}
else
{
uint8_t v_ignoreMissing_5619_; 
lean_dec(v___x_4876_);
v_ignoreMissing_5619_ = lean_ctor_get_uint8(v_a_4767_, sizeof(void*)*6 + 2);
if (v_ignoreMissing_5619_ == 0)
{
lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; uint8_t v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5620_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_dumpName___closed__1));
v___x_5621_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg___closed__0));
v___x_5622_ = lean_unsigned_to_nat(254u);
v___x_5623_ = lean_unsigned_to_nat(48u);
v___x_5624_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__1));
v___x_5625_ = 1;
v___x_5626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_c_4765_, v___x_5625_);
v___x_5627_ = lean_string_append(v___x_5624_, v___x_5626_);
lean_dec_ref(v___x_5626_);
v___x_5628_ = ((lean_object*)(l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___closed__2));
v___x_5629_ = lean_string_append(v___x_5627_, v___x_5628_);
v___x_5630_ = l_mkPanicMessageWithDecl(v___x_5620_, v___x_5621_, v___x_5622_, v___x_5623_, v___x_5629_);
lean_dec_ref(v___x_5629_);
v___x_5631_ = l_panic___at___00LeanExport_dumpConstant_spec__5(v___x_5630_, v_a_4766_, v_a_4767_);
return v___x_5631_;
}
else
{
lean_object* v___x_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; 
lean_dec(v_c_4765_);
v___x_5632_ = lean_box(0);
v___x_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5633_, 0, v___x_5632_);
lean_ctor_set(v___x_5633_, 1, v_a_4767_);
v___x_5634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
return v___x_5634_;
}
}
v___jp_4769_:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v___x_4770_ = lean_box(0);
v___x_4771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
lean_ctor_set(v___x_4771_, 1, v_a_4767_);
v___x_4772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
return v___x_4772_;
}
v___jp_4773_:
{
size_t v_sz_4779_; size_t v___x_4780_; lean_object* v___x_4781_; 
v_sz_4779_ = lean_array_size(v_fst_4777_);
v___x_4780_ = ((size_t)0ULL);
v___x_4781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_fst_4777_, v_sz_4779_, v___x_4780_, v___y_4774_, v_a_4766_, v_snd_4778_);
if (lean_obj_tag(v___x_4781_) == 0)
{
lean_object* v_a_4782_; lean_object* v_snd_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4873_; 
v_a_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc(v_a_4782_);
lean_dec_ref_known(v___x_4781_, 1);
v_snd_4783_ = lean_ctor_get(v_a_4782_, 1);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_a_4782_);
if (v_isSharedCheck_4873_ == 0)
{
lean_object* v_unused_4874_; 
v_unused_4874_ = lean_ctor_get(v_a_4782_, 0);
lean_dec(v_unused_4874_);
v___x_4785_ = v_a_4782_;
v_isShared_4786_ = v_isSharedCheck_4873_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_snd_4783_);
lean_dec(v_a_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4873_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4787_; 
v___x_4787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_fst_4777_, v_sz_4779_, v___x_4780_, v___y_4774_, v_a_4766_, v_snd_4783_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v_snd_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4871_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
v_snd_4789_ = lean_ctor_get(v_a_4788_, 1);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_a_4788_);
if (v_isSharedCheck_4871_ == 0)
{
lean_object* v_unused_4872_; 
v_unused_4872_ = lean_ctor_get(v_a_4788_, 0);
lean_dec(v_unused_4872_);
v___x_4791_ = v_a_4788_;
v_isShared_4792_ = v_isSharedCheck_4871_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_snd_4789_);
lean_dec(v_a_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4871_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
size_t v_sz_4793_; lean_object* v___x_4794_; 
v_sz_4793_ = lean_array_size(v___y_4776_);
v___x_4794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_4793_, v___x_4780_, v___y_4776_, v_a_4766_, v_snd_4789_);
if (lean_obj_tag(v___x_4794_) == 0)
{
lean_object* v_a_4795_; lean_object* v_fst_4796_; lean_object* v_snd_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4862_; 
v_a_4795_ = lean_ctor_get(v___x_4794_, 0);
lean_inc(v_a_4795_);
lean_dec_ref_known(v___x_4794_, 1);
v_fst_4796_ = lean_ctor_get(v_a_4795_, 0);
v_snd_4797_ = lean_ctor_get(v_a_4795_, 1);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_a_4795_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4799_ = v_a_4795_;
v_isShared_4800_ = v_isSharedCheck_4862_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_snd_4797_);
lean_inc(v_fst_4796_);
lean_dec(v_a_4795_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4862_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
size_t v_sz_4801_; lean_object* v___x_4802_; 
v_sz_4801_ = lean_array_size(v___y_4775_);
v___x_4802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_4801_, v___x_4780_, v___y_4775_, v_a_4766_, v_snd_4797_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v_fst_4804_; lean_object* v_snd_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4853_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref_known(v___x_4802_, 1);
v_fst_4804_ = lean_ctor_get(v_a_4803_, 0);
v_snd_4805_ = lean_ctor_get(v_a_4803_, 1);
v_isSharedCheck_4853_ = !lean_is_exclusive(v_a_4803_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4807_ = v_a_4803_;
v_isShared_4808_ = v_isSharedCheck_4853_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_snd_4805_);
lean_inc(v_fst_4804_);
lean_dec(v_a_4803_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4853_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; 
v___x_4809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_4779_, v___x_4780_, v_fst_4777_, v_a_4766_, v_snd_4805_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v_fst_4811_; lean_object* v_snd_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4844_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___x_4809_, 1);
v_fst_4811_ = lean_ctor_get(v_a_4810_, 0);
v_snd_4812_ = lean_ctor_get(v_a_4810_, 1);
v_isSharedCheck_4844_ = !lean_is_exclusive(v_a_4810_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4814_ = v_a_4810_;
v_isShared_4815_ = v_isSharedCheck_4844_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_snd_4812_);
lean_inc(v_fst_4811_);
lean_dec(v_a_4810_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4844_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4820_; 
v___x_4816_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__0));
v___x_4817_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__1));
v___x_4818_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4796_);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 1, v___x_4818_);
lean_ctor_set(v___x_4814_, 0, v___x_4817_);
v___x_4820_ = v___x_4814_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4817_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___closed__2));
v___x_4822_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4804_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 1, v___x_4822_);
lean_ctor_set(v___x_4807_, 0, v___x_4821_);
v___x_4824_ = v___x_4807_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4821_);
lean_ctor_set(v_reuseFailAlloc_4842_, 1, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4825_ = ((lean_object*)(l_LeanExport_dumpConstant___closed__2));
v___x_4826_ = l_Lean_Array_toJson___at___00LeanExport_dumpConstant_spec__19(v_fst_4811_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 1, v___x_4826_);
lean_ctor_set(v___x_4799_, 0, v___x_4825_);
v___x_4828_ = v___x_4799_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4829_ = lean_box(0);
if (v_isShared_4786_ == 0)
{
lean_ctor_set_tag(v___x_4785_, 1);
lean_ctor_set(v___x_4785_, 1, v___x_4829_);
lean_ctor_set(v___x_4785_, 0, v___x_4828_);
v___x_4831_ = v___x_4785_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v___x_4828_);
lean_ctor_set(v_reuseFailAlloc_4840_, 1, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4824_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4820_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Lean_Json_mkObj(v___x_4833_);
lean_dec_ref_known(v___x_4833_, 2);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 1, v___x_4834_);
lean_ctor_set(v___x_4791_, 0, v___x_4816_);
v___x_4836_ = v___x_4791_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4816_);
lean_ctor_set(v_reuseFailAlloc_4839_, 1, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4836_);
lean_ctor_set(v___x_4837_, 1, v___x_4829_);
v___x_4838_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpObj___redArg(v___x_4837_, v_snd_4812_);
lean_dec_ref_known(v___x_4837_, 2);
return v___x_4838_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
lean_del_object(v___x_4807_);
lean_dec(v_fst_4804_);
lean_del_object(v___x_4799_);
lean_dec(v_fst_4796_);
lean_del_object(v___x_4791_);
lean_del_object(v___x_4785_);
v_a_4845_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4809_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4809_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_del_object(v___x_4799_);
lean_dec(v_fst_4796_);
lean_del_object(v___x_4791_);
lean_del_object(v___x_4785_);
lean_dec_ref(v_fst_4777_);
v_a_4854_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4802_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4802_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
lean_del_object(v___x_4791_);
lean_del_object(v___x_4785_);
lean_dec_ref(v_fst_4777_);
lean_dec(v___y_4775_);
v_a_4863_ = lean_ctor_get(v___x_4794_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4794_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4794_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
}
else
{
lean_del_object(v___x_4785_);
lean_dec_ref(v_fst_4777_);
lean_dec(v___y_4776_);
lean_dec(v___y_4775_);
return v___x_4787_;
}
}
}
else
{
lean_dec_ref(v_fst_4777_);
lean_dec(v___y_4776_);
lean_dec(v___y_4775_);
return v___x_4781_;
}
}
}
}
LEAN_EXPORT void l_LeanExport_dumpConstant_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4765_ = stack[0].m_obj;
lean_object* v_a_4766_ = stack[1].m_obj;
lean_object* v_a_4767_ = stack[2].m_obj;
lean_object* v_res_5635_;
v_res_5635_ = l_LeanExport_dumpConstant(v_c_4765_, v_a_4766_, v_a_4767_);
stack->m_obj
 = v_res_5635_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(lean_object* v_as_5636_, size_t v_sz_5637_, size_t v_i_5638_, lean_object* v_b_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
uint8_t v___x_5643_; 
v___x_5643_ = lean_usize_dec_lt(v_i_5638_, v_sz_5637_);
if (v___x_5643_ == 0)
{
lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5644_, 0, v_b_5639_);
lean_ctor_set(v___x_5644_, 1, v___y_5641_);
v___x_5645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
return v___x_5645_;
}
else
{
lean_object* v___x_5646_; lean_object* v_a_5647_; lean_object* v___x_5648_; 
v___x_5646_ = lean_box(0);
v_a_5647_ = lean_array_uget_borrowed(v_as_5636_, v_i_5638_);
lean_inc(v_a_5647_);
v___x_5648_ = l_LeanExport_dumpConstant(v_a_5647_, v___y_5640_, v___y_5641_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v_snd_5650_; size_t v___x_5651_; size_t v___x_5652_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
lean_dec_ref_known(v___x_5648_, 1);
v_snd_5650_ = lean_ctor_get(v_a_5649_, 1);
lean_inc(v_snd_5650_);
lean_dec(v_a_5649_);
v___x_5651_ = ((size_t)1ULL);
v___x_5652_ = lean_usize_add(v_i_5638_, v___x_5651_);
v_i_5638_ = v___x_5652_;
v_b_5639_ = v___x_5646_;
v___y_5641_ = v_snd_5650_;
goto _start;
}
else
{
return v___x_5648_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5636_ = stack[0].m_obj;
size_t v_sz_5637_ = stack[1].m_num;
size_t v_i_5638_ = stack[2].m_num;
lean_object* v_b_5639_ = stack[3].m_obj;
lean_object* v___y_5640_ = stack[4].m_obj;
lean_object* v___y_5641_ = stack[5].m_obj;
lean_object* v_res_5654_;
v_res_5654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5636_, v_sz_5637_, v_i_5638_, v_b_5639_, v___y_5640_, v___y_5641_);
stack->m_obj
 = v_res_5654_;
}
lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(lean_object* v_e_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_){
_start:
{
lean_object* v___x_5659_; lean_object* v___x_5660_; size_t v_sz_5661_; size_t v___x_5662_; lean_object* v___x_5663_; 
v___x_5659_ = l_Lean_Expr_getUsedConstants(v_e_5655_);
v___x_5660_ = lean_box(0);
v_sz_5661_ = lean_array_size(v___x_5659_);
v___x_5662_ = ((size_t)0ULL);
v___x_5663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v___x_5659_, v_sz_5661_, v___x_5662_, v___x_5660_, v_a_5656_, v_a_5657_);
lean_dec_ref(v___x_5659_);
if (lean_obj_tag(v___x_5663_) == 0)
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5680_; 
v_a_5664_ = lean_ctor_get(v___x_5663_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5663_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5666_ = v___x_5663_;
v_isShared_5667_ = v_isSharedCheck_5680_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5663_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5680_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v_snd_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5678_; 
v_snd_5668_ = lean_ctor_get(v_a_5664_, 1);
v_isSharedCheck_5678_ = !lean_is_exclusive(v_a_5664_);
if (v_isSharedCheck_5678_ == 0)
{
lean_object* v_unused_5679_; 
v_unused_5679_ = lean_ctor_get(v_a_5664_, 0);
lean_dec(v_unused_5679_);
v___x_5670_ = v_a_5664_;
v_isShared_5671_ = v_isSharedCheck_5678_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_snd_5668_);
lean_dec(v_a_5664_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5678_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
lean_ctor_set(v___x_5670_, 0, v___x_5660_);
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v_snd_5668_);
v___x_5673_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
lean_object* v___x_5675_; 
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 0, v___x_5673_);
v___x_5675_ = v___x_5666_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5673_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
}
}
else
{
return v___x_5663_;
}
}
}
LEAN_EXPORT void l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_5655_ = stack[0].m_obj;
lean_object* v_a_5656_ = stack[1].m_obj;
lean_object* v_a_5657_ = stack[2].m_obj;
lean_object* v_res_5681_;
v_res_5681_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5655_, v_a_5656_, v_a_5657_);
stack->m_obj
 = v_res_5681_;
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps___boxed(lean_object* v_e_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_){
_start:
{
lean_object* v_res_5686_; 
v_res_5686_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps(v_e_5682_, v_a_5683_, v_a_5684_);
lean_dec_ref(v_a_5683_);
return v_res_5686_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg___boxed(lean_object* v_as_x27_5687_, lean_object* v_b_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
lean_object* v_res_5692_; 
v_res_5692_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5687_, v_b_5688_, v___y_5689_, v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v_as_x27_5687_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg___boxed(lean_object* v_as_x27_5693_, lean_object* v_b_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5693_, v_b_5694_, v___y_5695_, v___y_5696_);
lean_dec_ref(v___y_5695_);
lean_dec(v_as_x27_5693_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2___boxed(lean_object* v_x_5699_, lean_object* v_x_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v_res_5704_; 
v_res_5704_ = l_List_mapM_loop___at___00LeanExport_dumpConstant_spec__2(v_x_5699_, v_x_5700_, v___y_5701_, v___y_5702_);
lean_dec_ref(v___y_5701_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0___boxed(lean_object* v_as_5705_, lean_object* v_sz_5706_, lean_object* v_i_5707_, lean_object* v_b_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_){
_start:
{
size_t v_sz_boxed_5712_; size_t v_i_boxed_5713_; lean_object* v_res_5714_; 
v_sz_boxed_5712_ = lean_unbox_usize(v_sz_5706_);
lean_dec(v_sz_5706_);
v_i_boxed_5713_ = lean_unbox_usize(v_i_5707_);
lean_dec(v_i_5707_);
v_res_5714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpDeps_spec__0(v_as_5705_, v_sz_boxed_5712_, v_i_boxed_5713_, v_b_5708_, v___y_5709_, v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec_ref(v_as_5705_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps___boxed(lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_){
_start:
{
lean_object* v_res_5718_; 
v_res_5718_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpNatDeps(v_a_5715_, v_a_5716_);
lean_dec_ref(v_a_5715_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15___boxed(lean_object* v_as_5719_, lean_object* v_sz_5720_, lean_object* v_i_5721_, lean_object* v_b_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
size_t v_sz_boxed_5726_; size_t v_i_boxed_5727_; lean_object* v_res_5728_; 
v_sz_boxed_5726_ = lean_unbox_usize(v_sz_5720_);
lean_dec(v_sz_5720_);
v_i_boxed_5727_ = lean_unbox_usize(v_i_5721_);
lean_dec(v_i_5721_);
v_res_5728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__15(v_as_5719_, v_sz_boxed_5726_, v_i_boxed_5727_, v_b_5722_, v___y_5723_, v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec_ref(v_as_5719_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExpr___boxed(lean_object* v_e_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l_LeanExport_dumpExpr(v_e_5729_, v_a_5730_, v_a_5731_);
lean_dec_ref(v_a_5730_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14___boxed(lean_object* v_as_5734_, lean_object* v_sz_5735_, lean_object* v_i_5736_, lean_object* v_b_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_){
_start:
{
size_t v_sz_boxed_5741_; size_t v_i_boxed_5742_; lean_object* v_res_5743_; 
v_sz_boxed_5741_ = lean_unbox_usize(v_sz_5735_);
lean_dec(v_sz_5735_);
v_i_boxed_5742_ = lean_unbox_usize(v_i_5736_);
lean_dec(v_i_5736_);
v_res_5743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__14(v_as_5734_, v_sz_boxed_5741_, v_i_boxed_5742_, v_b_5737_, v___y_5738_, v___y_5739_);
lean_dec_ref(v___y_5738_);
lean_dec_ref(v_as_5734_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20___boxed(lean_object* v_as_5744_, lean_object* v_sz_5745_, lean_object* v_i_5746_, lean_object* v_b_5747_, lean_object* v___y_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_){
_start:
{
size_t v_sz_boxed_5751_; size_t v_i_boxed_5752_; lean_object* v_res_5753_; 
v_sz_boxed_5751_ = lean_unbox_usize(v_sz_5745_);
lean_dec(v_sz_5745_);
v_i_boxed_5752_ = lean_unbox_usize(v_i_5746_);
lean_dec(v_i_5746_);
v_res_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00LeanExport_dumpConstant_spec__20(v_as_5744_, v_sz_boxed_5751_, v_i_boxed_5752_, v_b_5747_, v___y_5748_, v___y_5749_);
lean_dec_ref(v___y_5748_);
lean_dec_ref(v_as_5744_);
return v_res_5753_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule___boxed(lean_object* v_rule_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l___private_LeanExport_Basic_0__LeanExport_dumpConstant_dumpRecRule(v_rule_5754_, v_a_5755_, v_a_5756_);
lean_dec_ref(v_a_5755_);
return v_res_5758_;
}
}
LEAN_EXPORT lean_object* l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps___boxed(lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_){
_start:
{
lean_object* v_res_5762_; 
v_res_5762_ = l___private_LeanExport_Basic_0__LeanExport_dumpExprAux_dumpStrDeps(v_a_5759_, v_a_5760_);
lean_dec_ref(v_a_5759_);
return v_res_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17___boxed(lean_object* v_sz_5763_, lean_object* v_i_5764_, lean_object* v_bs_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_){
_start:
{
size_t v_sz_boxed_5769_; size_t v_i_boxed_5770_; lean_object* v_res_5771_; 
v_sz_boxed_5769_ = lean_unbox_usize(v_sz_5763_);
lean_dec(v_sz_5763_);
v_i_boxed_5770_ = lean_unbox_usize(v_i_5764_);
lean_dec(v_i_5764_);
v_res_5771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__17(v_sz_boxed_5769_, v_i_boxed_5770_, v_bs_5765_, v___y_5766_, v___y_5767_);
lean_dec_ref(v___y_5766_);
return v_res_5771_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg___boxed(lean_object* v___x_5772_, lean_object* v_as_x27_5773_, lean_object* v_b_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
uint8_t v___x_173351__boxed_5778_; lean_object* v_res_5779_; 
v___x_173351__boxed_5778_ = lean_unbox(v___x_5772_);
v_res_5779_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_173351__boxed_5778_, v_as_x27_5773_, v_b_5774_, v___y_5775_, v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v_as_x27_5773_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16___boxed(lean_object* v_sz_5780_, lean_object* v_i_5781_, lean_object* v_bs_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_){
_start:
{
size_t v_sz_boxed_5786_; size_t v_i_boxed_5787_; lean_object* v_res_5788_; 
v_sz_boxed_5786_ = lean_unbox_usize(v_sz_5780_);
lean_dec(v_sz_5780_);
v_i_boxed_5787_ = lean_unbox_usize(v_i_5781_);
lean_dec(v_i_5781_);
v_res_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__16(v_sz_boxed_5786_, v_i_boxed_5787_, v_bs_5782_, v___y_5783_, v___y_5784_);
lean_dec_ref(v___y_5783_);
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18___boxed(lean_object* v_sz_5789_, lean_object* v_i_5790_, lean_object* v_bs_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_){
_start:
{
size_t v_sz_boxed_5795_; size_t v_i_boxed_5796_; lean_object* v_res_5797_; 
v_sz_boxed_5795_ = lean_unbox_usize(v_sz_5789_);
lean_dec(v_sz_5789_);
v_i_boxed_5796_ = lean_unbox_usize(v_i_5790_);
lean_dec(v_i_5790_);
v_res_5797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00LeanExport_dumpConstant_spec__18(v_sz_boxed_5795_, v_i_boxed_5796_, v_bs_5791_, v___y_5792_, v___y_5793_);
lean_dec_ref(v___y_5792_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg___boxed(lean_object* v___x_5798_, lean_object* v_val_5799_, lean_object* v_as_x27_5800_, lean_object* v_b_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
uint8_t v___x_173656__boxed_5805_; lean_object* v_res_5806_; 
v___x_173656__boxed_5805_ = lean_unbox(v___x_5798_);
v_res_5806_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_173656__boxed_5805_, v_val_5799_, v_as_x27_5800_, v_b_5801_, v___y_5802_, v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v_as_x27_5800_);
lean_dec_ref(v_val_5799_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpExprAux___boxed(lean_object* v_e_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l_LeanExport_dumpExprAux(v_e_5807_, v_a_5808_, v_a_5809_);
lean_dec_ref(v_a_5808_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l_LeanExport_dumpConstant___boxed(lean_object* v_c_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_){
_start:
{
lean_object* v_res_5816_; 
v_res_5816_ = l_LeanExport_dumpConstant(v_c_5812_, v_a_5813_, v_a_5814_);
lean_dec_ref(v_a_5813_);
return v_res_5816_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(uint8_t v___x_5817_, lean_object* v_as_5818_, lean_object* v_as_x27_5819_, lean_object* v_b_5820_, lean_object* v_a_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_){
_start:
{
lean_object* v___x_5825_; 
v___x_5825_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___redArg(v___x_5817_, v_as_x27_5819_, v_b_5820_, v___y_5822_, v___y_5823_);
return v___x_5825_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5817_ = stack[0].m_num;
lean_object* v_as_5818_ = stack[1].m_obj;
lean_object* v_as_x27_5819_ = stack[2].m_obj;
lean_object* v_b_5820_ = stack[3].m_obj;
lean_object* v___y_5822_ = stack[5].m_obj;
lean_object* v___y_5823_ = stack[6].m_obj;
lean_object* v_res_5826_;
v_res_5826_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_5817_, v_as_5818_, v_as_x27_5819_, v_b_5820_, lean_box(0), v___y_5822_, v___y_5823_);
stack->m_obj
 = v_res_5826_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7___boxed(lean_object* v___x_5827_, lean_object* v_as_5828_, lean_object* v_as_x27_5829_, lean_object* v_b_5830_, lean_object* v_a_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_){
_start:
{
uint8_t v___x_180806__boxed_5835_; lean_object* v_res_5836_; 
v___x_180806__boxed_5835_ = lean_unbox(v___x_5827_);
v_res_5836_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__7(v___x_180806__boxed_5835_, v_as_5828_, v_as_x27_5829_, v_b_5830_, v_a_5831_, v___y_5832_, v___y_5833_);
lean_dec_ref(v___y_5832_);
lean_dec(v_as_x27_5829_);
lean_dec(v_as_5828_);
return v_res_5836_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(uint8_t v___y_5837_, uint8_t v___x_5838_, lean_object* v_as_5839_, lean_object* v_as_x27_5840_, lean_object* v_b_5841_, lean_object* v_a_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
lean_object* v___x_5846_; 
v___x_5846_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___redArg(v___y_5837_, v___x_5838_, v_as_x27_5840_, v_b_5841_, v___y_5843_, v___y_5844_);
return v___x_5846_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_5837_ = stack[0].m_num;
uint8_t v___x_5838_ = stack[1].m_num;
lean_object* v_as_5839_ = stack[2].m_obj;
lean_object* v_as_x27_5840_ = stack[3].m_obj;
lean_object* v_b_5841_ = stack[4].m_obj;
lean_object* v___y_5843_ = stack[6].m_obj;
lean_object* v___y_5844_ = stack[7].m_obj;
lean_object* v_res_5847_;
v_res_5847_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_5837_, v___x_5838_, v_as_5839_, v_as_x27_5840_, v_b_5841_, lean_box(0), v___y_5843_, v___y_5844_);
stack->m_obj
 = v_res_5847_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9___boxed(lean_object* v___y_5848_, lean_object* v___x_5849_, lean_object* v_as_5850_, lean_object* v_as_x27_5851_, lean_object* v_b_5852_, lean_object* v_a_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_){
_start:
{
uint8_t v___y_180834__boxed_5857_; uint8_t v___x_180835__boxed_5858_; lean_object* v_res_5859_; 
v___y_180834__boxed_5857_ = lean_unbox(v___y_5848_);
v___x_180835__boxed_5858_ = lean_unbox(v___x_5849_);
v_res_5859_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__9(v___y_180834__boxed_5857_, v___x_180835__boxed_5858_, v_as_5850_, v_as_x27_5851_, v_b_5852_, v_a_5853_, v___y_5854_, v___y_5855_);
lean_dec_ref(v___y_5854_);
lean_dec(v_as_x27_5851_);
lean_dec(v_as_5850_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(lean_object* v_00_u03b4_5860_, lean_object* v_t_5861_, lean_object* v_k_5862_){
_start:
{
lean_object* v___x_5863_; 
v___x_5863_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___redArg(v_t_5861_, v_k_5862_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10___boxed(lean_object* v_00_u03b4_5864_, lean_object* v_t_5865_, lean_object* v_k_5866_){
_start:
{
lean_object* v_res_5867_; 
v_res_5867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00LeanExport_dumpConstant_spec__10(v_00_u03b4_5864_, v_t_5865_, v_k_5866_);
lean_dec(v_k_5866_);
lean_dec(v_t_5865_);
return v_res_5867_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(uint8_t v___x_5868_, lean_object* v_val_5869_, lean_object* v_as_5870_, lean_object* v_as_x27_5871_, lean_object* v_b_5872_, lean_object* v_a_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_){
_start:
{
lean_object* v___x_5877_; 
v___x_5877_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___redArg(v___x_5868_, v_val_5869_, v_as_x27_5871_, v_b_5872_, v___y_5874_, v___y_5875_);
return v___x_5877_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_5868_ = stack[0].m_num;
lean_object* v_val_5869_ = stack[1].m_obj;
lean_object* v_as_5870_ = stack[2].m_obj;
lean_object* v_as_x27_5871_ = stack[3].m_obj;
lean_object* v_b_5872_ = stack[4].m_obj;
lean_object* v___y_5874_ = stack[6].m_obj;
lean_object* v___y_5875_ = stack[7].m_obj;
lean_object* v_res_5878_;
v_res_5878_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_5868_, v_val_5869_, v_as_5870_, v_as_x27_5871_, v_b_5872_, lean_box(0), v___y_5874_, v___y_5875_);
stack->m_obj
 = v_res_5878_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12___boxed(lean_object* v___x_5879_, lean_object* v_val_5880_, lean_object* v_as_5881_, lean_object* v_as_x27_5882_, lean_object* v_b_5883_, lean_object* v_a_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_){
_start:
{
uint8_t v___x_180870__boxed_5888_; lean_object* v_res_5889_; 
v___x_180870__boxed_5888_ = lean_unbox(v___x_5879_);
v_res_5889_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__12(v___x_180870__boxed_5888_, v_val_5880_, v_as_5881_, v_as_x27_5882_, v_b_5883_, v_a_5884_, v___y_5885_, v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec(v_as_x27_5882_);
lean_dec(v_as_5881_);
lean_dec_ref(v_val_5880_);
return v_res_5889_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(lean_object* v_as_5890_, lean_object* v_as_x27_5891_, lean_object* v_b_5892_, lean_object* v_a_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_){
_start:
{
lean_object* v___x_5897_; 
v___x_5897_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___redArg(v_as_x27_5891_, v_b_5892_, v___y_5894_, v___y_5895_);
return v___x_5897_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5890_ = stack[0].m_obj;
lean_object* v_as_x27_5891_ = stack[1].m_obj;
lean_object* v_b_5892_ = stack[2].m_obj;
lean_object* v___y_5894_ = stack[4].m_obj;
lean_object* v___y_5895_ = stack[5].m_obj;
lean_object* v_res_5898_;
v_res_5898_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5890_, v_as_x27_5891_, v_b_5892_, lean_box(0), v___y_5894_, v___y_5895_);
stack->m_obj
 = v_res_5898_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13___boxed(lean_object* v_as_5899_, lean_object* v_as_x27_5900_, lean_object* v_b_5901_, lean_object* v_a_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__13(v_as_5899_, v_as_x27_5900_, v_b_5901_, v_a_5902_, v___y_5903_, v___y_5904_);
lean_dec_ref(v___y_5903_);
lean_dec(v_as_x27_5900_);
lean_dec(v_as_5899_);
return v_res_5906_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(lean_object* v_as_5907_, lean_object* v_as_x27_5908_, lean_object* v_b_5909_, lean_object* v_a_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_){
_start:
{
lean_object* v___x_5914_; 
v___x_5914_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___redArg(v_as_x27_5908_, v_b_5909_, v___y_5911_, v___y_5912_);
return v___x_5914_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5907_ = stack[0].m_obj;
lean_object* v_as_x27_5908_ = stack[1].m_obj;
lean_object* v_b_5909_ = stack[2].m_obj;
lean_object* v___y_5911_ = stack[4].m_obj;
lean_object* v___y_5912_ = stack[5].m_obj;
lean_object* v_res_5915_;
v_res_5915_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5907_, v_as_x27_5908_, v_b_5909_, lean_box(0), v___y_5911_, v___y_5912_);
stack->m_obj
 = v_res_5915_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22___boxed(lean_object* v_as_5916_, lean_object* v_as_x27_5917_, lean_object* v_b_5918_, lean_object* v_a_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_List_forIn_x27_loop___at___00LeanExport_dumpConstant_spec__22(v_as_5916_, v_as_x27_5917_, v_b_5918_, v_a_5919_, v___y_5920_, v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v_as_x27_5917_);
lean_dec(v_as_5916_);
return v_res_5923_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1(void){
_start:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5925_ = l_Lean_versionString;
v___x_5926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5926_, 0, v___x_5925_);
return v___x_5926_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2(void){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5927_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__1);
v___x_5928_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__0));
v___x_5929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5929_, 0, v___x_5928_);
lean_ctor_set(v___x_5929_, 1, v___x_5927_);
return v___x_5929_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4(void){
_start:
{
lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5931_ = l_Lean_githash;
v___x_5932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
return v___x_5932_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5(void){
_start:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; 
v___x_5933_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__4);
v___x_5934_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__3));
v___x_5935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5934_);
lean_ctor_set(v___x_5935_, 1, v___x_5933_);
return v___x_5935_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6(void){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
v___x_5936_ = lean_box(0);
v___x_5937_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__5);
v___x_5938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set(v___x_5938_, 1, v___x_5936_);
return v___x_5938_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7(void){
_start:
{
lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5939_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__6);
v___x_5940_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__2);
v___x_5941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5940_);
lean_ctor_set(v___x_5941_, 1, v___x_5939_);
return v___x_5941_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8(void){
_start:
{
lean_object* v___x_5942_; lean_object* v_leanMeta_5943_; 
v___x_5942_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__7);
v_leanMeta_5943_ = l_Lean_Json_mkObj(v___x_5942_);
return v_leanMeta_5943_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17(void){
_start:
{
lean_object* v___x_5962_; lean_object* v_exporterMeta_5963_; 
v___x_5962_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__16));
v_exporterMeta_5963_ = l_Lean_Json_mkObj(v___x_5962_);
return v_exporterMeta_5963_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18(void){
_start:
{
lean_object* v___x_5964_; lean_object* v_formatMeta_5965_; 
v___x_5964_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__15));
v_formatMeta_5965_ = l_Lean_Json_mkObj(v___x_5964_);
return v_formatMeta_5965_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21(void){
_start:
{
lean_object* v_exporterMeta_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; 
v_exporterMeta_5968_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__17);
v___x_5969_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__20));
v___x_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5969_);
lean_ctor_set(v___x_5970_, 1, v_exporterMeta_5968_);
return v___x_5970_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23(void){
_start:
{
lean_object* v_leanMeta_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; 
v_leanMeta_5972_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__8);
v___x_5973_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__22));
v___x_5974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5973_);
lean_ctor_set(v___x_5974_, 1, v_leanMeta_5972_);
return v___x_5974_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25(void){
_start:
{
lean_object* v_formatMeta_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v_formatMeta_5976_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__18);
v___x_5977_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__24));
v___x_5978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5977_);
lean_ctor_set(v___x_5978_, 1, v_formatMeta_5976_);
return v___x_5978_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; 
v___x_5979_ = lean_box(0);
v___x_5980_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__25);
v___x_5981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5981_, 0, v___x_5980_);
lean_ctor_set(v___x_5981_, 1, v___x_5979_);
return v___x_5981_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; 
v___x_5982_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__26);
v___x_5983_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__23);
v___x_5984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5983_);
lean_ctor_set(v___x_5984_, 1, v___x_5982_);
return v___x_5984_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28(void){
_start:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5985_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__27);
v___x_5986_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__21);
v___x_5987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
lean_ctor_set(v___x_5987_, 1, v___x_5985_);
return v___x_5987_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5988_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__28);
v___x_5989_ = l_Lean_Json_mkObj(v___x_5988_);
return v___x_5989_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30(void){
_start:
{
lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5990_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__29);
v___x_5991_ = ((lean_object*)(l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__19));
v___x_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5992_, 0, v___x_5991_);
lean_ctor_set(v___x_5992_, 1, v___x_5990_);
return v___x_5992_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31(void){
_start:
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5993_ = lean_box(0);
v___x_5994_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__30);
v___x_5995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5995_, 0, v___x_5994_);
lean_ctor_set(v___x_5995_, 1, v___x_5993_);
return v___x_5995_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32(void){
_start:
{
lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5996_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__31);
v___x_5997_ = l_Lean_Json_mkObj(v___x_5996_);
return v___x_5997_;
}
}
static lean_object* _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata(void){
_start:
{
lean_object* v___x_5998_; 
v___x_5998_ = lean_obj_once(&l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32, &l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32_once, _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata___closed__32);
return v___x_5998_;
}
}
static lean_object* _init_l_LeanExport_dumpMetadata___redArg___closed__0(void){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5999_ = l___private_LeanExport_Basic_0__LeanExport_exportMetadata;
v___x_6000_ = l_Lean_Json_compress(v___x_5999_);
return v___x_6000_;
}
}
lean_object* l_LeanExport_dumpMetadata___redArg(lean_object* v_a_6001_){
_start:
{
lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_6003_ = lean_obj_once(&l_LeanExport_dumpMetadata___redArg___closed__0, &l_LeanExport_dumpMetadata___redArg___closed__0_once, _init_l_LeanExport_dumpMetadata___redArg___closed__0);
v___x_6004_ = l_IO_println___at___00__private_LeanExport_Basic_0__LeanExport_dumpName_spec__1(v___x_6003_);
if (lean_obj_tag(v___x_6004_) == 0)
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6013_; 
v_a_6005_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6007_ = v___x_6004_;
v_isShared_6008_ = v_isSharedCheck_6013_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_6004_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6013_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6009_; lean_object* v___x_6011_; 
v___x_6009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6009_, 0, v_a_6005_);
lean_ctor_set(v___x_6009_, 1, v_a_6001_);
if (v_isShared_6008_ == 0)
{
lean_ctor_set(v___x_6007_, 0, v___x_6009_);
v___x_6011_ = v___x_6007_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_6009_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
else
{
lean_object* v_a_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6021_; 
lean_dec_ref(v_a_6001_);
v_a_6014_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_6016_ = v___x_6004_;
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_a_6014_);
lean_dec(v___x_6004_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6019_; 
if (v_isShared_6017_ == 0)
{
v___x_6019_ = v___x_6016_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_a_6014_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
return v___x_6019_;
}
}
}
}
}
LEAN_EXPORT void l_LeanExport_dumpMetadata___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_6001_ = stack[0].m_obj;
lean_object* v_res_6022_;
v_res_6022_ = l_LeanExport_dumpMetadata___redArg(v_a_6001_);
stack->m_obj
 = v_res_6022_;
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___redArg___boxed(lean_object* v_a_6023_, lean_object* v_a_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_LeanExport_dumpMetadata___redArg(v_a_6023_);
return v_res_6025_;
}
}
lean_object* l_LeanExport_dumpMetadata(lean_object* v_a_6026_, lean_object* v_a_6027_){
_start:
{
lean_object* v___x_6029_; 
v___x_6029_ = l_LeanExport_dumpMetadata___redArg(v_a_6027_);
return v___x_6029_;
}
}
LEAN_EXPORT void l_LeanExport_dumpMetadata_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_6026_ = stack[0].m_obj;
lean_object* v_a_6027_ = stack[1].m_obj;
lean_object* v_res_6030_;
v_res_6030_ = l_LeanExport_dumpMetadata(v_a_6026_, v_a_6027_);
stack->m_obj
 = v_res_6030_;
}
LEAN_EXPORT lean_object* l_LeanExport_dumpMetadata___boxed(lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_){
_start:
{
lean_object* v_res_6034_; 
v_res_6034_ = l_LeanExport_dumpMetadata(v_a_6031_, v_a_6032_);
lean_dec_ref(v_a_6031_);
return v_res_6034_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(lean_object* v_as_x27_6035_, lean_object* v_b_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_){
_start:
{
if (lean_obj_tag(v_as_x27_6035_) == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6040_, 0, v_b_6036_);
lean_ctor_set(v___x_6040_, 1, v___y_6038_);
v___x_6041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6040_);
return v___x_6041_;
}
else
{
lean_object* v_head_6042_; lean_object* v_tail_6043_; lean_object* v_visitedNames_6044_; lean_object* v_visitedLevels_6045_; lean_object* v_visitedExprs_6046_; lean_object* v_visitedConstants_6047_; uint8_t v_exportMData_6048_; uint8_t v_exportUnsafe_6049_; uint8_t v_ignoreMissing_6050_; lean_object* v_recursorMap_6051_; lean_object* v___x_6053_; uint8_t v_isShared_6054_; uint8_t v_isSharedCheck_6064_; 
v_head_6042_ = lean_ctor_get(v_as_x27_6035_, 0);
v_tail_6043_ = lean_ctor_get(v_as_x27_6035_, 1);
v_visitedNames_6044_ = lean_ctor_get(v___y_6038_, 0);
v_visitedLevels_6045_ = lean_ctor_get(v___y_6038_, 1);
v_visitedExprs_6046_ = lean_ctor_get(v___y_6038_, 2);
v_visitedConstants_6047_ = lean_ctor_get(v___y_6038_, 3);
v_exportMData_6048_ = lean_ctor_get_uint8(v___y_6038_, sizeof(void*)*6);
v_exportUnsafe_6049_ = lean_ctor_get_uint8(v___y_6038_, sizeof(void*)*6 + 1);
v_ignoreMissing_6050_ = lean_ctor_get_uint8(v___y_6038_, sizeof(void*)*6 + 2);
v_recursorMap_6051_ = lean_ctor_get(v___y_6038_, 5);
v_isSharedCheck_6064_ = !lean_is_exclusive(v___y_6038_);
if (v_isSharedCheck_6064_ == 0)
{
lean_object* v_unused_6065_; 
v_unused_6065_ = lean_ctor_get(v___y_6038_, 4);
lean_dec(v_unused_6065_);
v___x_6053_ = v___y_6038_;
v_isShared_6054_ = v_isSharedCheck_6064_;
goto v_resetjp_6052_;
}
else
{
lean_inc(v_recursorMap_6051_);
lean_inc(v_visitedConstants_6047_);
lean_inc(v_visitedExprs_6046_);
lean_inc(v_visitedLevels_6045_);
lean_inc(v_visitedNames_6044_);
lean_dec(v___y_6038_);
v___x_6053_ = lean_box(0);
v_isShared_6054_ = v_isSharedCheck_6064_;
goto v_resetjp_6052_;
}
v_resetjp_6052_:
{
lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6058_; 
v___x_6055_ = lean_box(0);
v___x_6056_ = lean_obj_once(&l_LeanExport_dumpExpr___closed__1, &l_LeanExport_dumpExpr___closed__1_once, _init_l_LeanExport_dumpExpr___closed__1);
if (v_isShared_6054_ == 0)
{
lean_ctor_set(v___x_6053_, 4, v___x_6056_);
v___x_6058_ = v___x_6053_;
goto v_reusejp_6057_;
}
else
{
lean_object* v_reuseFailAlloc_6063_; 
v_reuseFailAlloc_6063_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_6063_, 0, v_visitedNames_6044_);
lean_ctor_set(v_reuseFailAlloc_6063_, 1, v_visitedLevels_6045_);
lean_ctor_set(v_reuseFailAlloc_6063_, 2, v_visitedExprs_6046_);
lean_ctor_set(v_reuseFailAlloc_6063_, 3, v_visitedConstants_6047_);
lean_ctor_set(v_reuseFailAlloc_6063_, 4, v___x_6056_);
lean_ctor_set(v_reuseFailAlloc_6063_, 5, v_recursorMap_6051_);
lean_ctor_set_uint8(v_reuseFailAlloc_6063_, sizeof(void*)*6, v_exportMData_6048_);
lean_ctor_set_uint8(v_reuseFailAlloc_6063_, sizeof(void*)*6 + 1, v_exportUnsafe_6049_);
lean_ctor_set_uint8(v_reuseFailAlloc_6063_, sizeof(void*)*6 + 2, v_ignoreMissing_6050_);
v___x_6058_ = v_reuseFailAlloc_6063_;
goto v_reusejp_6057_;
}
v_reusejp_6057_:
{
lean_object* v___x_6059_; 
lean_inc(v_head_6042_);
v___x_6059_ = l_LeanExport_dumpConstant(v_head_6042_, v___y_6037_, v___x_6058_);
if (lean_obj_tag(v___x_6059_) == 0)
{
lean_object* v_a_6060_; lean_object* v_snd_6061_; 
v_a_6060_ = lean_ctor_get(v___x_6059_, 0);
lean_inc(v_a_6060_);
lean_dec_ref_known(v___x_6059_, 1);
v_snd_6061_ = lean_ctor_get(v_a_6060_, 1);
lean_inc(v_snd_6061_);
lean_dec(v_a_6060_);
v_as_x27_6035_ = v_tail_6043_;
v_b_6036_ = v___x_6055_;
v___y_6038_ = v_snd_6061_;
goto _start;
}
else
{
return v___x_6059_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_6035_ = stack[0].m_obj;
lean_object* v_b_6036_ = stack[1].m_obj;
lean_object* v___y_6037_ = stack[2].m_obj;
lean_object* v___y_6038_ = stack[3].m_obj;
lean_object* v_res_6066_;
v_res_6066_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6035_, v_b_6036_, v___y_6037_, v___y_6038_);
stack->m_obj
 = v_res_6066_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg___boxed(lean_object* v_as_x27_6067_, lean_object* v_b_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_){
_start:
{
lean_object* v_res_6072_; 
v_res_6072_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6067_, v_b_6068_, v___y_6069_, v___y_6070_);
lean_dec_ref(v___y_6069_);
lean_dec(v_as_x27_6067_);
return v_res_6072_;
}
}
lean_object* l_LeanExport_dumpEnv___lam__0(lean_object* v_env_6073_, lean_object* v_cliOptions_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_){
_start:
{
lean_object* v___x_6079_; 
v___x_6079_ = l_LeanExport_initState(v_env_6073_, v_cliOptions_6074_, v___y_6076_, v___y_6077_);
if (lean_obj_tag(v___x_6079_) == 0)
{
lean_object* v_a_6080_; lean_object* v_snd_6081_; lean_object* v___x_6082_; 
v_a_6080_ = lean_ctor_get(v___x_6079_, 0);
lean_inc(v_a_6080_);
lean_dec_ref_known(v___x_6079_, 1);
v_snd_6081_ = lean_ctor_get(v_a_6080_, 1);
lean_inc(v_snd_6081_);
lean_dec(v_a_6080_);
v___x_6082_ = l_LeanExport_dumpMetadata___redArg(v_snd_6081_);
if (lean_obj_tag(v___x_6082_) == 0)
{
lean_object* v_a_6083_; lean_object* v_snd_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; 
v_a_6083_ = lean_ctor_get(v___x_6082_, 0);
lean_inc(v_a_6083_);
lean_dec_ref_known(v___x_6082_, 1);
v_snd_6084_ = lean_ctor_get(v_a_6083_, 1);
lean_inc(v_snd_6084_);
lean_dec(v_a_6083_);
v___x_6085_ = lean_box(0);
v___x_6086_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v___y_6075_, v___x_6085_, v___y_6076_, v_snd_6084_);
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6103_; 
v_a_6087_ = lean_ctor_get(v___x_6086_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v___x_6086_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6089_ = v___x_6086_;
v_isShared_6090_ = v_isSharedCheck_6103_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6086_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6103_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v_snd_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6101_; 
v_snd_6091_ = lean_ctor_get(v_a_6087_, 1);
v_isSharedCheck_6101_ = !lean_is_exclusive(v_a_6087_);
if (v_isSharedCheck_6101_ == 0)
{
lean_object* v_unused_6102_; 
v_unused_6102_ = lean_ctor_get(v_a_6087_, 0);
lean_dec(v_unused_6102_);
v___x_6093_ = v_a_6087_;
v_isShared_6094_ = v_isSharedCheck_6101_;
goto v_resetjp_6092_;
}
else
{
lean_inc(v_snd_6091_);
lean_dec(v_a_6087_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6101_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
lean_object* v___x_6096_; 
if (v_isShared_6094_ == 0)
{
lean_ctor_set(v___x_6093_, 0, v___x_6085_);
v___x_6096_ = v___x_6093_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6100_; 
v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6085_);
lean_ctor_set(v_reuseFailAlloc_6100_, 1, v_snd_6091_);
v___x_6096_ = v_reuseFailAlloc_6100_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
lean_object* v___x_6098_; 
if (v_isShared_6090_ == 0)
{
lean_ctor_set(v___x_6089_, 0, v___x_6096_);
v___x_6098_ = v___x_6089_;
goto v_reusejp_6097_;
}
else
{
lean_object* v_reuseFailAlloc_6099_; 
v_reuseFailAlloc_6099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6099_, 0, v___x_6096_);
v___x_6098_ = v_reuseFailAlloc_6099_;
goto v_reusejp_6097_;
}
v_reusejp_6097_:
{
return v___x_6098_;
}
}
}
}
}
else
{
return v___x_6086_;
}
}
else
{
return v___x_6082_;
}
}
else
{
return v___x_6079_;
}
}
}
LEAN_EXPORT void l_LeanExport_dumpEnv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_6073_ = stack[0].m_obj;
lean_object* v_cliOptions_6074_ = stack[1].m_obj;
lean_object* v___y_6075_ = stack[2].m_obj;
lean_object* v___y_6076_ = stack[3].m_obj;
lean_object* v___y_6077_ = stack[4].m_obj;
lean_object* v_res_6104_;
v_res_6104_ = l_LeanExport_dumpEnv___lam__0(v_env_6073_, v_cliOptions_6074_, v___y_6075_, v___y_6076_, v___y_6077_);
stack->m_obj
 = v_res_6104_;
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___lam__0___boxed(lean_object* v_env_6105_, lean_object* v_cliOptions_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
lean_object* v_res_6111_; 
v_res_6111_ = l_LeanExport_dumpEnv___lam__0(v_env_6105_, v_cliOptions_6106_, v___y_6107_, v___y_6108_, v___y_6109_);
lean_dec_ref(v___y_6108_);
lean_dec(v___y_6107_);
lean_dec(v_cliOptions_6106_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___lam__0(lean_object* v_es_6112_, lean_object* v_a_6113_, lean_object* v_b_6114_){
_start:
{
lean_object* v___x_6115_; lean_object* v___x_6116_; 
v___x_6115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6115_, 0, v_a_6113_);
lean_ctor_set(v___x_6115_, 1, v_b_6114_);
v___x_6116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6115_);
lean_ctor_set(v___x_6116_, 1, v_es_6112_);
return v___x_6116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(lean_object* v_f_6117_, lean_object* v_x_6118_, lean_object* v_x_6119_){
_start:
{
if (lean_obj_tag(v_x_6119_) == 0)
{
lean_dec(v_f_6117_);
return v_x_6118_;
}
else
{
lean_object* v_key_6120_; lean_object* v_value_6121_; lean_object* v_tail_6122_; lean_object* v___x_6123_; 
v_key_6120_ = lean_ctor_get(v_x_6119_, 0);
lean_inc(v_key_6120_);
v_value_6121_ = lean_ctor_get(v_x_6119_, 1);
lean_inc(v_value_6121_);
v_tail_6122_ = lean_ctor_get(v_x_6119_, 2);
lean_inc(v_tail_6122_);
lean_dec_ref_known(v_x_6119_, 3);
lean_inc(v_f_6117_);
v___x_6123_ = lean_apply_3(v_f_6117_, v_x_6118_, v_key_6120_, v_value_6121_);
v_x_6118_ = v___x_6123_;
v_x_6119_ = v_tail_6122_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(lean_object* v_f_6125_, lean_object* v_as_6126_, size_t v_i_6127_, size_t v_stop_6128_, lean_object* v_b_6129_){
_start:
{
uint8_t v___x_6130_; 
v___x_6130_ = lean_usize_dec_eq(v_i_6127_, v_stop_6128_);
if (v___x_6130_ == 0)
{
lean_object* v___x_6131_; lean_object* v___x_6132_; size_t v___x_6133_; size_t v___x_6134_; 
v___x_6131_ = lean_array_uget_borrowed(v_as_6126_, v_i_6127_);
lean_inc(v___x_6131_);
lean_inc(v_f_6125_);
v___x_6132_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6125_, v_b_6129_, v___x_6131_);
v___x_6133_ = ((size_t)1ULL);
v___x_6134_ = lean_usize_add(v_i_6127_, v___x_6133_);
v_i_6127_ = v___x_6134_;
v_b_6129_ = v___x_6132_;
goto _start;
}
else
{
lean_dec(v_f_6125_);
return v_b_6129_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6125_ = stack[0].m_obj;
lean_object* v_as_6126_ = stack[1].m_obj;
size_t v_i_6127_ = stack[2].m_num;
size_t v_stop_6128_ = stack[3].m_num;
lean_object* v_b_6129_ = stack[4].m_obj;
lean_object* v_res_6136_;
v_res_6136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6125_, v_as_6126_, v_i_6127_, v_stop_6128_, v_b_6129_);
stack->m_obj
 = v_res_6136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_f_6137_, lean_object* v_as_6138_, lean_object* v_i_6139_, lean_object* v_stop_6140_, lean_object* v_b_6141_){
_start:
{
size_t v_i_boxed_6142_; size_t v_stop_boxed_6143_; lean_object* v_res_6144_; 
v_i_boxed_6142_ = lean_unbox_usize(v_i_6139_);
lean_dec(v_i_6139_);
v_stop_boxed_6143_ = lean_unbox_usize(v_stop_6140_);
lean_dec(v_stop_6140_);
v_res_6144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6137_, v_as_6138_, v_i_boxed_6142_, v_stop_boxed_6143_, v_b_6141_);
lean_dec_ref(v_as_6138_);
return v_res_6144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0(lean_object* v_f_6145_, lean_object* v_x1_6146_, lean_object* v_x2_6147_, lean_object* v_x3_6148_){
_start:
{
lean_object* v___x_6149_; 
v___x_6149_ = lean_apply_3(v_f_6145_, v_x1_6146_, v_x2_6147_, v_x3_6148_);
return v___x_6149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(lean_object* v_f_6150_, lean_object* v_keys_6151_, lean_object* v_vals_6152_, lean_object* v_i_6153_, lean_object* v_acc_6154_){
_start:
{
lean_object* v___x_6155_; uint8_t v___x_6156_; 
v___x_6155_ = lean_array_get_size(v_keys_6151_);
v___x_6156_ = lean_nat_dec_lt(v_i_6153_, v___x_6155_);
if (v___x_6156_ == 0)
{
lean_dec(v_i_6153_);
lean_dec(v_f_6150_);
return v_acc_6154_;
}
else
{
lean_object* v_k_6157_; lean_object* v_v_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; 
v_k_6157_ = lean_array_fget_borrowed(v_keys_6151_, v_i_6153_);
v_v_6158_ = lean_array_fget_borrowed(v_vals_6152_, v_i_6153_);
lean_inc(v_f_6150_);
lean_inc(v_v_6158_);
lean_inc(v_k_6157_);
v___x_6159_ = lean_apply_3(v_f_6150_, v_acc_6154_, v_k_6157_, v_v_6158_);
v___x_6160_ = lean_unsigned_to_nat(1u);
v___x_6161_ = lean_nat_add(v_i_6153_, v___x_6160_);
lean_dec(v_i_6153_);
v_i_6153_ = v___x_6161_;
v_acc_6154_ = v___x_6159_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg___boxed(lean_object* v_f_6163_, lean_object* v_keys_6164_, lean_object* v_vals_6165_, lean_object* v_i_6166_, lean_object* v_acc_6167_){
_start:
{
lean_object* v_res_6168_; 
v_res_6168_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6163_, v_keys_6164_, v_vals_6165_, v_i_6166_, v_acc_6167_);
lean_dec_ref(v_vals_6165_);
lean_dec_ref(v_keys_6164_);
return v_res_6168_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(lean_object* v_f_6169_, lean_object* v_as_6170_, size_t v_i_6171_, size_t v_stop_6172_, lean_object* v_b_6173_){
_start:
{
lean_object* v___y_6175_; uint8_t v___x_6179_; 
v___x_6179_ = lean_usize_dec_eq(v_i_6171_, v_stop_6172_);
if (v___x_6179_ == 0)
{
lean_object* v___x_6180_; 
v___x_6180_ = lean_array_uget_borrowed(v_as_6170_, v_i_6171_);
switch(lean_obj_tag(v___x_6180_))
{
case 0:
{
lean_object* v_key_6181_; lean_object* v_val_6182_; lean_object* v___x_6183_; 
v_key_6181_ = lean_ctor_get(v___x_6180_, 0);
v_val_6182_ = lean_ctor_get(v___x_6180_, 1);
lean_inc(v_f_6169_);
lean_inc(v_val_6182_);
lean_inc(v_key_6181_);
v___x_6183_ = lean_apply_3(v_f_6169_, v_b_6173_, v_key_6181_, v_val_6182_);
v___y_6175_ = v___x_6183_;
goto v___jp_6174_;
}
case 1:
{
lean_object* v_node_6184_; lean_object* v___x_6185_; 
v_node_6184_ = lean_ctor_get(v___x_6180_, 0);
lean_inc(v_f_6169_);
v___x_6185_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6169_, v_node_6184_, v_b_6173_);
v___y_6175_ = v___x_6185_;
goto v___jp_6174_;
}
default: 
{
v___y_6175_ = v_b_6173_;
goto v___jp_6174_;
}
}
}
else
{
lean_dec(v_f_6169_);
return v_b_6173_;
}
v___jp_6174_:
{
size_t v___x_6176_; size_t v___x_6177_; 
v___x_6176_ = ((size_t)1ULL);
v___x_6177_ = lean_usize_add(v_i_6171_, v___x_6176_);
v_i_6171_ = v___x_6177_;
v_b_6173_ = v___y_6175_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6169_ = stack[0].m_obj;
lean_object* v_as_6170_ = stack[1].m_obj;
size_t v_i_6171_ = stack[2].m_num;
size_t v_stop_6172_ = stack[3].m_num;
lean_object* v_b_6173_ = stack[4].m_obj;
lean_object* v_res_6186_;
v_res_6186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6169_, v_as_6170_, v_i_6171_, v_stop_6172_, v_b_6173_);
stack->m_obj
 = v_res_6186_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_f_6187_, lean_object* v_x_6188_, lean_object* v_x_6189_){
_start:
{
if (lean_obj_tag(v_x_6188_) == 0)
{
lean_object* v_es_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; uint8_t v___x_6193_; 
v_es_6190_ = lean_ctor_get(v_x_6188_, 0);
v___x_6191_ = lean_unsigned_to_nat(0u);
v___x_6192_ = lean_array_get_size(v_es_6190_);
v___x_6193_ = lean_nat_dec_lt(v___x_6191_, v___x_6192_);
if (v___x_6193_ == 0)
{
lean_dec(v_f_6187_);
return v_x_6189_;
}
else
{
size_t v___x_6194_; size_t v___x_6195_; lean_object* v___x_6196_; 
v___x_6194_ = ((size_t)0ULL);
v___x_6195_ = lean_usize_of_nat(v___x_6192_);
v___x_6196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6187_, v_es_6190_, v___x_6194_, v___x_6195_, v_x_6189_);
return v___x_6196_;
}
}
else
{
lean_object* v_ks_6197_; lean_object* v_vs_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v_ks_6197_ = lean_ctor_get(v_x_6188_, 0);
v_vs_6198_ = lean_ctor_get(v_x_6188_, 1);
v___x_6199_ = lean_unsigned_to_nat(0u);
v___x_6200_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6187_, v_ks_6197_, v_vs_6198_, v___x_6199_, v_x_6189_);
return v___x_6200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg___boxed(lean_object* v_f_6201_, lean_object* v_x_6202_, lean_object* v_x_6203_){
_start:
{
lean_object* v_res_6204_; 
v_res_6204_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6201_, v_x_6202_, v_x_6203_);
lean_dec_ref(v_x_6202_);
return v_res_6204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_f_6205_, lean_object* v_as_6206_, lean_object* v_i_6207_, lean_object* v_stop_6208_, lean_object* v_b_6209_){
_start:
{
size_t v_i_boxed_6210_; size_t v_stop_boxed_6211_; lean_object* v_res_6212_; 
v_i_boxed_6210_ = lean_unbox_usize(v_i_6207_);
lean_dec(v_i_6207_);
v_stop_boxed_6211_ = lean_unbox_usize(v_stop_6208_);
lean_dec(v_stop_6208_);
v_res_6212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6205_, v_as_6206_, v_i_boxed_6210_, v_stop_boxed_6211_, v_b_6209_);
lean_dec_ref(v_as_6206_);
return v_res_6212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(lean_object* v_map_6213_, lean_object* v_f_6214_, lean_object* v_init_6215_){
_start:
{
lean_object* v___f_6216_; lean_object* v___x_6217_; 
v___f_6216_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___lam__0), 4, 1);
lean_closure_set(v___f_6216_, 0, v_f_6214_);
v___x_6217_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v___f_6216_, v_map_6213_, v_init_6215_);
return v___x_6217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_map_6218_, lean_object* v_f_6219_, lean_object* v_init_6220_){
_start:
{
lean_object* v_res_6221_; 
v_res_6221_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6218_, v_f_6219_, v_init_6220_);
lean_dec_ref(v_map_6218_);
return v_res_6221_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(lean_object* v_f_6222_, lean_object* v_init_6223_, lean_object* v_m_6224_){
_start:
{
lean_object* v_map_u2081_6225_; lean_object* v_map_u2082_6226_; lean_object* v_buckets_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; uint8_t v___x_6230_; 
v_map_u2081_6225_ = lean_ctor_get(v_m_6224_, 0);
v_map_u2082_6226_ = lean_ctor_get(v_m_6224_, 1);
v_buckets_6227_ = lean_ctor_get(v_map_u2081_6225_, 1);
v___x_6228_ = lean_unsigned_to_nat(0u);
v___x_6229_ = lean_array_get_size(v_buckets_6227_);
v___x_6230_ = lean_nat_dec_lt(v___x_6228_, v___x_6229_);
if (v___x_6230_ == 0)
{
lean_object* v___x_6231_; 
v___x_6231_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6226_, v_f_6222_, v_init_6223_);
return v___x_6231_;
}
else
{
size_t v___x_6232_; size_t v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; 
v___x_6232_ = ((size_t)0ULL);
v___x_6233_ = lean_usize_of_nat(v___x_6229_);
lean_inc(v_f_6222_);
v___x_6234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6222_, v_buckets_6227_, v___x_6232_, v___x_6233_, v_init_6223_);
v___x_6235_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_u2082_6226_, v_f_6222_, v___x_6234_);
return v___x_6235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg___boxed(lean_object* v_f_6236_, lean_object* v_init_6237_, lean_object* v_m_6238_){
_start:
{
lean_object* v_res_6239_; 
v_res_6239_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6236_, v_init_6237_, v_m_6238_);
lean_dec_ref(v_m_6238_);
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(lean_object* v_m_6241_){
_start:
{
lean_object* v___f_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___f_6242_ = ((lean_object*)(l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___closed__0));
v___x_6243_ = lean_box(0);
v___x_6244_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v___f_6242_, v___x_6243_, v_m_6241_);
return v___x_6244_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg___boxed(lean_object* v_m_6245_){
_start:
{
lean_object* v_res_6246_; 
v_res_6246_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6245_);
lean_dec_ref(v_m_6245_);
return v_res_6246_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(lean_object* v_a_6247_, lean_object* v_a_6248_){
_start:
{
if (lean_obj_tag(v_a_6247_) == 0)
{
lean_object* v___x_6249_; 
v___x_6249_ = l_List_reverse___redArg(v_a_6248_);
return v___x_6249_;
}
else
{
lean_object* v_head_6250_; lean_object* v_tail_6251_; lean_object* v___x_6253_; uint8_t v_isShared_6254_; uint8_t v_isSharedCheck_6261_; 
v_head_6250_ = lean_ctor_get(v_a_6247_, 0);
v_tail_6251_ = lean_ctor_get(v_a_6247_, 1);
v_isSharedCheck_6261_ = !lean_is_exclusive(v_a_6247_);
if (v_isSharedCheck_6261_ == 0)
{
v___x_6253_ = v_a_6247_;
v_isShared_6254_ = v_isSharedCheck_6261_;
goto v_resetjp_6252_;
}
else
{
lean_inc(v_tail_6251_);
lean_inc(v_head_6250_);
lean_dec(v_a_6247_);
v___x_6253_ = lean_box(0);
v_isShared_6254_ = v_isSharedCheck_6261_;
goto v_resetjp_6252_;
}
v_resetjp_6252_:
{
uint8_t v___x_6255_; 
v___x_6255_ = l_Lean_Name_isInternal(v_head_6250_);
if (v___x_6255_ == 0)
{
lean_object* v___x_6257_; 
if (v_isShared_6254_ == 0)
{
lean_ctor_set(v___x_6253_, 1, v_a_6248_);
v___x_6257_ = v___x_6253_;
goto v_reusejp_6256_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_head_6250_);
lean_ctor_set(v_reuseFailAlloc_6259_, 1, v_a_6248_);
v___x_6257_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6256_;
}
v_reusejp_6256_:
{
v_a_6247_ = v_tail_6251_;
v_a_6248_ = v___x_6257_;
goto _start;
}
}
else
{
lean_del_object(v___x_6253_);
lean_dec(v_head_6250_);
v_a_6247_ = v_tail_6251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(lean_object* v_a_6262_, lean_object* v_a_6263_){
_start:
{
if (lean_obj_tag(v_a_6262_) == 0)
{
lean_object* v___x_6264_; 
v___x_6264_ = l_List_reverse___redArg(v_a_6263_);
return v___x_6264_;
}
else
{
lean_object* v_head_6265_; lean_object* v_tail_6266_; lean_object* v___x_6268_; uint8_t v_isShared_6269_; uint8_t v_isSharedCheck_6275_; 
v_head_6265_ = lean_ctor_get(v_a_6262_, 0);
v_tail_6266_ = lean_ctor_get(v_a_6262_, 1);
v_isSharedCheck_6275_ = !lean_is_exclusive(v_a_6262_);
if (v_isSharedCheck_6275_ == 0)
{
v___x_6268_ = v_a_6262_;
v_isShared_6269_ = v_isSharedCheck_6275_;
goto v_resetjp_6267_;
}
else
{
lean_inc(v_tail_6266_);
lean_inc(v_head_6265_);
lean_dec(v_a_6262_);
v___x_6268_ = lean_box(0);
v_isShared_6269_ = v_isSharedCheck_6275_;
goto v_resetjp_6267_;
}
v_resetjp_6267_:
{
lean_object* v_fst_6270_; lean_object* v___x_6272_; 
v_fst_6270_ = lean_ctor_get(v_head_6265_, 0);
lean_inc(v_fst_6270_);
lean_dec(v_head_6265_);
if (v_isShared_6269_ == 0)
{
lean_ctor_set(v___x_6268_, 1, v_a_6263_);
lean_ctor_set(v___x_6268_, 0, v_fst_6270_);
v___x_6272_ = v___x_6268_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v_fst_6270_);
lean_ctor_set(v_reuseFailAlloc_6274_, 1, v_a_6263_);
v___x_6272_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
v_a_6262_ = v_tail_6266_;
v_a_6263_ = v___x_6272_;
goto _start;
}
}
}
}
}
lean_object* l_LeanExport_dumpEnv(lean_object* v_env_6276_, lean_object* v_constants_x3f_6277_, lean_object* v_cliOptions_6278_){
_start:
{
lean_object* v___y_6281_; 
if (lean_obj_tag(v_constants_x3f_6277_) == 0)
{
lean_object* v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; 
lean_inc_ref(v_env_6276_);
v___x_6284_ = l_Lean_Environment_constants(v_env_6276_);
v___x_6285_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v___x_6284_);
lean_dec_ref(v___x_6284_);
v___x_6286_ = lean_box(0);
v___x_6287_ = l_List_mapTR_loop___at___00LeanExport_dumpEnv_spec__2(v___x_6285_, v___x_6286_);
v___x_6288_ = l_List_filterTR_loop___at___00LeanExport_dumpEnv_spec__3(v___x_6287_, v___x_6286_);
v___y_6281_ = v___x_6288_;
goto v___jp_6280_;
}
else
{
lean_object* v_val_6289_; 
v_val_6289_ = lean_ctor_get(v_constants_x3f_6277_, 0);
lean_inc(v_val_6289_);
lean_dec_ref_known(v_constants_x3f_6277_, 1);
v___y_6281_ = v_val_6289_;
goto v___jp_6280_;
}
v___jp_6280_:
{
lean_object* v___f_6282_; lean_object* v___x_6283_; 
lean_inc_ref(v_env_6276_);
v___f_6282_ = lean_alloc_closure((void*)(l_LeanExport_dumpEnv___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6282_, 0, v_env_6276_);
lean_closure_set(v___f_6282_, 1, v_cliOptions_6278_);
lean_closure_set(v___f_6282_, 2, v___y_6281_);
v___x_6283_ = l_LeanExport_M_run___redArg(v_env_6276_, v___f_6282_);
return v___x_6283_;
}
}
}
LEAN_EXPORT void l_LeanExport_dumpEnv_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_6276_ = stack[0].m_obj;
lean_object* v_constants_x3f_6277_ = stack[1].m_obj;
lean_object* v_cliOptions_6278_ = stack[2].m_obj;
lean_object* v_res_6290_;
v_res_6290_ = l_LeanExport_dumpEnv(v_env_6276_, v_constants_x3f_6277_, v_cliOptions_6278_);
stack->m_obj
 = v_res_6290_;
}
LEAN_EXPORT lean_object* l_LeanExport_dumpEnv___boxed(lean_object* v_env_6291_, lean_object* v_constants_x3f_6292_, lean_object* v_cliOptions_6293_, lean_object* v_a_6294_){
_start:
{
lean_object* v_res_6295_; 
v_res_6295_ = l_LeanExport_dumpEnv(v_env_6291_, v_constants_x3f_6292_, v_cliOptions_6293_);
return v_res_6295_;
}
}
lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(lean_object* v_as_6296_, lean_object* v_as_x27_6297_, lean_object* v_b_6298_, lean_object* v_a_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_){
_start:
{
lean_object* v___x_6303_; 
v___x_6303_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___redArg(v_as_x27_6297_, v_b_6298_, v___y_6300_, v___y_6301_);
return v___x_6303_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_6296_ = stack[0].m_obj;
lean_object* v_as_x27_6297_ = stack[1].m_obj;
lean_object* v_b_6298_ = stack[2].m_obj;
lean_object* v___y_6300_ = stack[4].m_obj;
lean_object* v___y_6301_ = stack[5].m_obj;
lean_object* v_res_6304_;
v_res_6304_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6296_, v_as_x27_6297_, v_b_6298_, lean_box(0), v___y_6300_, v___y_6301_);
stack->m_obj
 = v_res_6304_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0___boxed(lean_object* v_as_6305_, lean_object* v_as_x27_6306_, lean_object* v_b_6307_, lean_object* v_a_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_){
_start:
{
lean_object* v_res_6312_; 
v_res_6312_ = l_List_forIn_x27_loop___at___00LeanExport_dumpEnv_spec__0(v_as_6305_, v_as_x27_6306_, v_b_6307_, v_a_6308_, v___y_6309_, v___y_6310_);
lean_dec_ref(v___y_6309_);
lean_dec(v_as_x27_6306_);
lean_dec(v_as_6305_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(lean_object* v_00_u03b2_6313_, lean_object* v_m_6314_){
_start:
{
lean_object* v___x_6315_; 
v___x_6315_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___redArg(v_m_6314_);
return v___x_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1___boxed(lean_object* v_00_u03b2_6316_, lean_object* v_m_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l_Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1(v_00_u03b2_6316_, v_m_6317_);
lean_dec_ref(v_m_6317_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(lean_object* v_00_u03b2_6319_, lean_object* v_00_u03c3_6320_, lean_object* v_f_6321_, lean_object* v_init_6322_, lean_object* v_m_6323_){
_start:
{
lean_object* v___x_6324_; 
v___x_6324_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___redArg(v_f_6321_, v_init_6322_, v_m_6323_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1___boxed(lean_object* v_00_u03b2_6325_, lean_object* v_00_u03c3_6326_, lean_object* v_f_6327_, lean_object* v_init_6328_, lean_object* v_m_6329_){
_start:
{
lean_object* v_res_6330_; 
v_res_6330_ = l_Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1(v_00_u03b2_6325_, v_00_u03c3_6326_, v_f_6327_, v_init_6328_, v_m_6329_);
lean_dec_ref(v_m_6329_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_6331_, lean_object* v_00_u03c3_6332_, lean_object* v_f_6333_, lean_object* v_x_6334_, lean_object* v_x_6335_){
_start:
{
lean_object* v___x_6336_; 
v___x_6336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__2___redArg(v_f_6333_, v_x_6334_, v_x_6335_);
return v___x_6336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(lean_object* v_00_u03c3_6337_, lean_object* v_00_u03b2_6338_, lean_object* v_map_6339_, lean_object* v_f_6340_, lean_object* v_init_6341_){
_start:
{
lean_object* v___x_6342_; 
v___x_6342_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___redArg(v_map_6339_, v_f_6340_, v_init_6341_);
return v___x_6342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03c3_6343_, lean_object* v_00_u03b2_6344_, lean_object* v_map_6345_, lean_object* v_f_6346_, lean_object* v_init_6347_){
_start:
{
lean_object* v_res_6348_; 
v_res_6348_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3(v_00_u03c3_6343_, v_00_u03b2_6344_, v_map_6345_, v_f_6346_, v_init_6347_);
lean_dec_ref(v_map_6345_);
return v_res_6348_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_6349_, lean_object* v_00_u03c3_6350_, lean_object* v_f_6351_, lean_object* v_as_6352_, size_t v_i_6353_, size_t v_stop_6354_, lean_object* v_b_6355_){
_start:
{
lean_object* v___x_6356_; 
v___x_6356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___redArg(v_f_6351_, v_as_6352_, v_i_6353_, v_stop_6354_, v_b_6355_);
return v___x_6356_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6351_ = stack[2].m_obj;
lean_object* v_as_6352_ = stack[3].m_obj;
size_t v_i_6353_ = stack[4].m_num;
size_t v_stop_6354_ = stack[5].m_num;
lean_object* v_b_6355_ = stack[6].m_obj;
lean_object* v_res_6357_;
v_res_6357_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(lean_box(0), lean_box(0), v_f_6351_, v_as_6352_, v_i_6353_, v_stop_6354_, v_b_6355_);
stack->m_obj
 = v_res_6357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4___boxed(lean_object* v_00_u03b2_6358_, lean_object* v_00_u03c3_6359_, lean_object* v_f_6360_, lean_object* v_as_6361_, lean_object* v_i_6362_, lean_object* v_stop_6363_, lean_object* v_b_6364_){
_start:
{
size_t v_i_boxed_6365_; size_t v_stop_boxed_6366_; lean_object* v_res_6367_; 
v_i_boxed_6365_ = lean_unbox_usize(v_i_6362_);
lean_dec(v_i_6362_);
v_stop_boxed_6366_ = lean_unbox_usize(v_stop_6363_);
lean_dec(v_stop_6363_);
v_res_6367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__4(v_00_u03b2_6358_, v_00_u03c3_6359_, v_f_6360_, v_as_6361_, v_i_boxed_6365_, v_stop_boxed_6366_, v_b_6364_);
lean_dec_ref(v_as_6361_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_map_6368_, lean_object* v_f_6369_, lean_object* v_init_6370_){
_start:
{
lean_object* v___x_6371_; 
v___x_6371_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6369_, v_map_6368_, v_init_6370_);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_map_6372_, lean_object* v_f_6373_, lean_object* v_init_6374_){
_start:
{
lean_object* v_res_6375_; 
v_res_6375_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___redArg(v_map_6372_, v_f_6373_, v_init_6374_);
lean_dec_ref(v_map_6372_);
return v_res_6375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03c3_6376_, lean_object* v_00_u03b2_6377_, lean_object* v_map_6378_, lean_object* v_f_6379_, lean_object* v_init_6380_){
_start:
{
lean_object* v___x_6381_; 
v___x_6381_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6379_, v_map_6378_, v_init_6380_);
return v___x_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03c3_6382_, lean_object* v_00_u03b2_6383_, lean_object* v_map_6384_, lean_object* v_f_6385_, lean_object* v_init_6386_){
_start:
{
lean_object* v_res_6387_; 
v_res_6387_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6(v_00_u03c3_6382_, v_00_u03b2_6383_, v_map_6384_, v_f_6385_, v_init_6386_);
lean_dec_ref(v_map_6384_);
return v_res_6387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03c3_6388_, lean_object* v_00_u03b1_6389_, lean_object* v_00_u03b2_6390_, lean_object* v_f_6391_, lean_object* v_x_6392_, lean_object* v_x_6393_){
_start:
{
lean_object* v___x_6394_; 
v___x_6394_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_f_6391_, v_x_6392_, v_x_6393_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7___boxed(lean_object* v_00_u03c3_6395_, lean_object* v_00_u03b1_6396_, lean_object* v_00_u03b2_6397_, lean_object* v_f_6398_, lean_object* v_x_6399_, lean_object* v_x_6400_){
_start:
{
lean_object* v_res_6401_; 
v_res_6401_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7(v_00_u03c3_6395_, v_00_u03b1_6396_, v_00_u03b2_6397_, v_f_6398_, v_x_6399_, v_x_6400_);
lean_dec_ref(v_x_6399_);
return v_res_6401_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_object* v_00_u03b1_6402_, lean_object* v_00_u03b2_6403_, lean_object* v_00_u03c3_6404_, lean_object* v_f_6405_, lean_object* v_as_6406_, size_t v_i_6407_, size_t v_stop_6408_, lean_object* v_b_6409_){
_start:
{
lean_object* v___x_6410_; 
v___x_6410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___redArg(v_f_6405_, v_as_6406_, v_i_6407_, v_stop_6408_, v_b_6409_);
return v___x_6410_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_6405_ = stack[3].m_obj;
lean_object* v_as_6406_ = stack[4].m_obj;
size_t v_i_6407_ = stack[5].m_num;
size_t v_stop_6408_ = stack[6].m_num;
lean_object* v_b_6409_ = stack[7].m_obj;
lean_object* v_res_6411_;
v_res_6411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(lean_box(0), lean_box(0), lean_box(0), v_f_6405_, v_as_6406_, v_i_6407_, v_stop_6408_, v_b_6409_);
stack->m_obj
 = v_res_6411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b1_6412_, lean_object* v_00_u03b2_6413_, lean_object* v_00_u03c3_6414_, lean_object* v_f_6415_, lean_object* v_as_6416_, lean_object* v_i_6417_, lean_object* v_stop_6418_, lean_object* v_b_6419_){
_start:
{
size_t v_i_boxed_6420_; size_t v_stop_boxed_6421_; lean_object* v_res_6422_; 
v_i_boxed_6420_ = lean_unbox_usize(v_i_6417_);
lean_dec(v_i_6417_);
v_stop_boxed_6421_ = lean_unbox_usize(v_stop_6418_);
lean_dec(v_stop_6418_);
v_res_6422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__9(v_00_u03b1_6412_, v_00_u03b2_6413_, v_00_u03c3_6414_, v_f_6415_, v_as_6416_, v_i_boxed_6420_, v_stop_boxed_6421_, v_b_6419_);
lean_dec_ref(v_as_6416_);
return v_res_6422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(lean_object* v_00_u03c3_6423_, lean_object* v_00_u03b1_6424_, lean_object* v_00_u03b2_6425_, lean_object* v_f_6426_, lean_object* v_keys_6427_, lean_object* v_vals_6428_, lean_object* v_heq_6429_, lean_object* v_i_6430_, lean_object* v_acc_6431_){
_start:
{
lean_object* v___x_6432_; 
v___x_6432_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___redArg(v_f_6426_, v_keys_6427_, v_vals_6428_, v_i_6430_, v_acc_6431_);
return v___x_6432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10___boxed(lean_object* v_00_u03c3_6433_, lean_object* v_00_u03b1_6434_, lean_object* v_00_u03b2_6435_, lean_object* v_f_6436_, lean_object* v_keys_6437_, lean_object* v_vals_6438_, lean_object* v_heq_6439_, lean_object* v_i_6440_, lean_object* v_acc_6441_){
_start:
{
lean_object* v_res_6442_; 
v_res_6442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_SMap_toList___at___00LeanExport_dumpEnv_spec__1_spec__1_spec__3_spec__6_spec__7_spec__10(v_00_u03c3_6433_, v_00_u03b1_6434_, v_00_u03b2_6435_, v_f_6436_, v_keys_6437_, v_vals_6438_, v_heq_6439_, v_i_6440_, v_acc_6441_);
lean_dec_ref(v_vals_6438_);
lean_dec_ref(v_keys_6437_);
return v_res_6442_;
}
}
lean_object* runtime_initialize_Lean(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_LeanExport_Basic_0__LeanExport_exportMetadata = _init_l___private_LeanExport_Basic_0__LeanExport_exportMetadata();
lean_mark_persistent(l___private_LeanExport_Basic_0__LeanExport_exportMetadata);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_LeanExport_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
