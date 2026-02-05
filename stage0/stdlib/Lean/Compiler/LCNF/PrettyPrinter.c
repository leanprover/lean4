// Lean compiler output
// Module: Lean.Compiler.LCNF.PrettyPrinter
// Imports: public import Lean.PrettyPrinter.Delaborator.Options public import Lean.Compiler.LCNF.Internalize
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
lean_object* l_Std_Format_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1_value;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8;
static lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9;
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "◾"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6;
static lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__5_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9_value;
extern lean_object* l_Lean_pp_explicit;
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
uint8_t l_Lean_Expr_isType0(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__0_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ctor_"};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__4_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__6_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo = (const lean_object*)&l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " # "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "uproj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sproj["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__10_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pap "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13_value;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@&"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__3_value;
extern lean_object* l_Lean_pp_funBinderTypes;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "let "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3_value;
extern lean_object* l_Lean_pp_letVarTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " :="};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "fun "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "jp "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goto "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__6_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " =>"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "| _ =>"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppAlt___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cases "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__8_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "return "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__10_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__11_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊥"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__12_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__13 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__13_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = "⊥ : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__14_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__15_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "uset "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__16_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__18_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "] := "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__20_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sset "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__22_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "] : "};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__24_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppCode___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppCode___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_all;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1_value;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___closed__2;
extern lean_object* l_Lean_pp_sanitizeNames;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "def "};
static const lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3;
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_indentD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_indentD(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget_borrowed(x_11, x_12);
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_16);
x_17 = lean_apply_7(x_1, x_16, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_12, x_19);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_20);
x_21 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_3 = x_23;
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget_borrowed(x_25, x_26);
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_30);
x_31 = lean_apply_7(x_1, x_30, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_26, x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_27);
x_36 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_2 = x_35;
x_3 = x_38;
goto _start;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget_borrowed(x_1, x_9);
lean_inc_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc(x_14);
x_15 = lean_apply_7(x_2, x_14, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Array_toSubarray___redArg(x_1, x_17, x_10);
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_2, x_18, x_16, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_16 = lean_apply_7(x_1, x_15, x_7, x_8, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
lean_inc(x_2);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_array_size(x_2);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_3, x_1, x_2, x_11, x_12, x_10, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin_spec__0(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_getBinderName(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = 1;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 1;
x_15 = l_Lean_Name_toString(x_13, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_26 = l_Lean_Exception_isInterrupt(x_19);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_19);
x_20 = x_27;
goto block_25;
}
else
{
lean_dec(x_19);
x_20 = x_26;
goto block_25;
}
block_25:
{
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_7);
x_21 = 1;
x_22 = l_Lean_Name_toString(x_1, x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_dec(x_1);
return x_7;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_36 = l_Lean_Exception_isInterrupt(x_28);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_28);
x_30 = x_37;
goto block_35;
}
else
{
lean_dec(x_28);
x_30 = x_36;
goto block_35;
}
block_35:
{
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_29);
x_31 = 1;
x_32 = l_Lean_Name_toString(x_1, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_dec(x_1);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppFVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5;
x_4 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8;
x_2 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4;
x_5 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_box(1);
x_7 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_8 = 0;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0;
x_11 = lean_box(0);
x_12 = 1;
x_13 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set(x_13, 4, x_11);
lean_ctor_set(x_13, 5, x_9);
lean_ctor_set(x_13, 6, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*7 + 2, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*7 + 3, x_12);
x_14 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9;
x_15 = lean_st_mk_ref(x_14);
x_16 = l_Lean_Meta_ppExpr(x_1, x_13, x_15, x_3, x_4);
lean_dec_ref(x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_st_ref_get(x_15);
lean_dec(x_15);
lean_dec(x_18);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_st_ref_get(x_15);
lean_dec(x_15);
lean_dec(x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
}
else
{
lean_dec(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Compiler_LCNF_PP_ppArg_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__4));
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_10, x_3, x_4, x_5, x_6);
return x_11;
}
default: 
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l_Lean_pp_explicit;
x_16 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_13);
lean_dec_ref(x_2);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
else
{
uint8_t x_18; 
lean_free_object(x_1);
x_18 = l_Lean_Expr_isConst(x_13);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isProp(x_13);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isType0(x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isFVar(x_13);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
x_26 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = 0;
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
x_35 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
return x_22;
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_5, x_6);
return x_43;
}
}
else
{
lean_object* x_44; 
x_44 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_5, x_6);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_5, x_6);
return x_45;
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_13, x_2, x_5, x_6);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_5, 2);
x_49 = l_Lean_pp_explicit;
x_50 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_47);
lean_dec_ref(x_2);
x_51 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__3));
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = l_Lean_Expr_isConst(x_47);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_isProp(x_47);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_isType0(x_47);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_isFVar(x_47);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_47, x_2, x_5, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
x_61 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = 0;
x_67 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_59)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_59;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
return x_57;
}
}
else
{
lean_object* x_69; 
x_69 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_47, x_2, x_5, x_6);
return x_69;
}
}
else
{
lean_object* x_70; 
x_70 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_47, x_2, x_5, x_6);
return x_70;
}
}
else
{
lean_object* x_71; 
x_71 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_47, x_2, x_5, x_6);
return x_71;
}
}
else
{
lean_object* x_72; 
x_72 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_47, x_2, x_5, x_6);
return x_72;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppArg___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PP_ppArg___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_10 = lean_box(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppArg___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_9, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppArgs(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(lean_object* x_1) {
_start:
{
uint64_t x_3; lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = l_Nat_reprFast(x_11);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Nat_reprFast(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_String_quote(x_19);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_String_quote(x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
case 2:
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_27 = lean_uint8_to_nat(x_26);
x_28 = l_Nat_reprFast(x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
case 3:
{
uint16_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_32 = lean_uint16_to_nat(x_31);
x_33 = l_Nat_reprFast(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
case 4:
{
uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_37 = lean_uint32_to_nat(x_36);
x_38 = l_Nat_reprFast(x_37);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
default: 
{
uint64_t x_41; 
x_41 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_3 = x_41;
x_4 = lean_box(0);
goto block_9;
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_uint64_to_nat(x_3);
x_6 = l_Nat_reprFast(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLitValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_ppLitValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_33; uint8_t x_34; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec_ref(x_1);
x_18 = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__5));
x_19 = l_Nat_reprFast(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_4);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_nat_dec_lt(x_33, x_5);
x_22 = x_35;
goto block_32;
}
else
{
x_22 = x_34;
goto block_32;
}
block_17:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = 1;
x_10 = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__1));
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Name_toString(x_2, x_9);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__3));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_dec(x_2);
return x_6;
}
}
block_32:
{
if (x_22 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
x_6 = x_21;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = ((lean_object*)(l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo___closed__7));
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Nat_reprFast(x_4);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = l_Nat_reprFast(x_5);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_6 = x_31;
goto block_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_instToFormatCtorInfo___private__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Compiler_LCNF_PP_ppLitValue___redArg(x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_11 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__1));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_3);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec_ref(x_2);
x_15 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_14, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Nat_reprFast(x_13);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__1));
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Nat_reprFast(x_13);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_dec(x_13);
return x_15;
}
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_32);
lean_dec_ref(x_2);
x_33 = l_Lean_Expr_const___override(x_30, x_31);
lean_inc_ref(x_3);
x_34 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_33, x_3, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_32);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_dec(x_35);
return x_36;
}
}
else
{
lean_dec_ref(x_32);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_34;
}
}
case 4:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_44, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_45, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_45);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_50);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_51);
lean_ctor_set(x_2, 0, x_47);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
else
{
lean_dec(x_47);
lean_free_object(x_2);
return x_48;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_45);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_46;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_55 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_53, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_54, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_58);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 1, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_dec(x_56);
return x_57;
}
}
else
{
lean_dec_ref(x_54);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_55;
}
}
}
case 5:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
x_65 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_64, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(x_63);
x_69 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
lean_ctor_set(x_2, 1, x_69);
lean_ctor_set(x_2, 0, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_65, 0, x_70);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(x_63);
x_73 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
lean_ctor_set(x_2, 1, x_73);
lean_ctor_set(x_2, 0, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_71);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_63);
return x_65;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_2, 0);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_2);
x_78 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_77, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_formatCtorInfo(x_76);
x_82 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
if (lean_is_scalar(x_80)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_80;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_dec_ref(x_76);
return x_78;
}
}
}
case 6:
{
uint8_t x_86; 
lean_dec_ref(x_3);
x_86 = !lean_is_exclusive(x_2);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_2, 0);
x_88 = lean_ctor_get(x_2, 1);
x_89 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_88, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
x_93 = l_Nat_reprFast(x_87);
x_94 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_94);
lean_ctor_set(x_2, 0, x_92);
x_95 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_89, 0, x_97);
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_89, 0);
lean_inc(x_98);
lean_dec(x_89);
x_99 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
x_100 = l_Nat_reprFast(x_87);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_101);
lean_ctor_set(x_2, 0, x_99);
x_102 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_2);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_87);
return x_89;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_2, 0);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_2);
x_108 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_107, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__3));
x_112 = l_Nat_reprFast(x_106);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
x_115 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_116 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 1, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
else
{
lean_dec(x_106);
return x_108;
}
}
}
case 7:
{
uint8_t x_119; 
lean_dec_ref(x_3);
x_119 = !lean_is_exclusive(x_2);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_2, 0);
x_121 = lean_ctor_get(x_2, 1);
x_122 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_121, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
x_126 = l_Nat_reprFast(x_120);
x_127 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_127);
lean_ctor_set(x_2, 0, x_125);
x_128 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_129 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_129, 0, x_2);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_124);
lean_ctor_set(x_122, 0, x_130);
return x_122;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_122, 0);
lean_inc(x_131);
lean_dec(x_122);
x_132 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
x_133 = l_Nat_reprFast(x_120);
x_134 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_134);
lean_ctor_set(x_2, 0, x_132);
x_135 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_2);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_131);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_120);
return x_122;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_2, 0);
x_140 = lean_ctor_get(x_2, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_2);
x_141 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_140, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__7));
x_145 = l_Nat_reprFast(x_139);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_142);
if (lean_is_scalar(x_143)) {
 x_151 = lean_alloc_ctor(0, 1, 0);
} else {
 x_151 = x_143;
}
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
else
{
lean_dec(x_139);
return x_141;
}
}
}
case 8:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_3);
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_inc(x_154);
lean_dec_ref(x_2);
x_155 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_154, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
x_159 = l_Nat_reprFast(x_152);
x_160 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
x_162 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Nat_reprFast(x_153);
x_165 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_155, 0, x_169);
return x_155;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_ctor_get(x_155, 0);
lean_inc(x_170);
lean_dec(x_155);
x_171 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__9));
x_172 = l_Nat_reprFast(x_152);
x_173 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_176 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Nat_reprFast(x_153);
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
x_180 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__5));
x_181 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_170);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
else
{
lean_dec(x_153);
lean_dec(x_152);
return x_155;
}
}
case 9:
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_2);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_2, 0);
x_186 = lean_ctor_get(x_2, 1);
x_187 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_186, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_186);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = 1;
x_191 = l_Lean_Name_toString(x_185, x_190);
x_192 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_189);
lean_ctor_set(x_2, 0, x_192);
lean_ctor_set(x_187, 0, x_2);
return x_187;
}
else
{
lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_187, 0);
lean_inc(x_193);
lean_dec(x_187);
x_194 = 1;
x_195 = l_Lean_Name_toString(x_185, x_194);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_193);
lean_ctor_set(x_2, 0, x_196);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_2);
return x_197;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_185);
return x_187;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_2, 0);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_2);
x_200 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_199, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = 1;
x_204 = l_Lean_Name_toString(x_198, x_203);
x_205 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_201);
if (lean_is_scalar(x_202)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_202;
}
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
else
{
lean_dec(x_198);
return x_200;
}
}
}
default: 
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_2);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_2, 0);
x_210 = lean_ctor_get(x_2, 1);
x_211 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_210, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_210);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
x_215 = 1;
x_216 = l_Lean_Name_toString(x_209, x_215);
x_217 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_217);
lean_ctor_set(x_2, 0, x_214);
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_2);
lean_ctor_set(x_218, 1, x_213);
lean_ctor_set(x_211, 0, x_218);
return x_211;
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_219 = lean_ctor_get(x_211, 0);
lean_inc(x_219);
lean_dec(x_211);
x_220 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
x_221 = 1;
x_222 = l_Lean_Name_toString(x_209, x_221);
x_223 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_223);
lean_ctor_set(x_2, 0, x_220);
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_2);
lean_ctor_set(x_224, 1, x_219);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
return x_225;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_209);
return x_211;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_2, 0);
x_227 = lean_ctor_get(x_2, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_2);
x_228 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_227, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__13));
x_232 = 1;
x_233 = l_Lean_Name_toString(x_226, x_232);
x_234 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_235, 0, x_231);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_229);
if (lean_is_scalar(x_230)) {
 x_237 = lean_alloc_ctor(0, 1, 0);
} else {
 x_237 = x_230;
}
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
else
{
lean_dec(x_226);
return x_228;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
if (x_8 == 0)
{
lean_object* x_54; 
x_54 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__2));
x_9 = x_54;
goto block_53;
}
else
{
lean_object* x_55; 
x_55 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__3));
x_9 = x_55;
goto block_53;
}
block_53:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 2);
x_11 = l_Lean_pp_funBinderTypes;
x_12 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_13 = 1;
x_14 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_6, x_13);
x_15 = lean_string_append(x_9, x_14);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Name_toString(x_6, x_12);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_9);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_28 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
x_29 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
lean_ctor_set(x_18, 0, x_35);
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = l_Lean_Name_toString(x_6, x_12);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_9);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7;
x_45 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__8));
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__9));
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
x_50 = 0;
x_51 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
else
{
lean_dec_ref(x_9);
lean_dec(x_6);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_PP_ppParam___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PP_ppParam___redArg(x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppParam(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_10 = lean_box(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppParam___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_9, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppParams(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_Lean_pp_letVarTypes;
x_11 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_1, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
x_18 = 1;
x_19 = l_Lean_Name_toString(x_12, x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
x_27 = 1;
x_28 = l_Lean_Name_toString(x_12, x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_dec(x_12);
return x_14;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_2, 3);
lean_inc(x_37);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_38 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_36, x_3, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_1, x_37, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
x_45 = l_Lean_Name_toString(x_35, x_11);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_45);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_38);
x_47 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
x_50 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_41, 0, x_52);
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
x_55 = l_Lean_Name_toString(x_35, x_11);
lean_ctor_set_tag(x_38, 3);
lean_ctor_set(x_38, 0, x_55);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_38);
x_57 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_40);
x_60 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
lean_free_object(x_38);
lean_dec(x_40);
lean_dec(x_35);
return x_41;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_38, 0);
lean_inc(x_64);
lean_dec(x_38);
x_65 = l_Lean_Compiler_LCNF_PP_ppLetValue(x_1, x_37, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__1));
x_69 = l_Lean_Name_toString(x_35, x_11);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_64);
x_75 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_66);
if (lean_is_scalar(x_67)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_67;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_dec(x_64);
lean_dec(x_35);
return x_65;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_mkFVar(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isErased(x_3);
if (x_7 == 0)
{
if (x_1 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_size(x_2);
x_9 = 0;
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_PP_getFunType_spec__0(x_8, x_9, x_2);
x_11 = l_Lean_Compiler_LCNF_instantiateForall(x_3, x_10, x_4, x_5);
lean_dec_ref(x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec_ref(x_2);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_getFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
x_8 = l_Lean_Compiler_LCNF_PP_getFunType(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_12 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_19 = 1;
x_20 = l_Lean_Name_toString(x_9, x_19);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 0, x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
x_23 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_Format_indentD(x_17);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
lean_dec(x_15);
x_28 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_29 = 1;
x_30 = l_Lean_Name_toString(x_9, x_29);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 0, x_30);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_12);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
x_33 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_Format_indentD(x_27);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
else
{
lean_free_object(x_12);
lean_dec(x_14);
lean_dec(x_9);
return x_15;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_43 = 1;
x_44 = l_Lean_Name_toString(x_9, x_43);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
x_48 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Std_Format_indentD(x_40);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_41)) {
 x_52 = lean_alloc_ctor(0, 1, 0);
} else {
 x_52 = x_41;
}
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
else
{
lean_dec(x_38);
lean_dec(x_9);
return x_39;
}
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
case 1:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
x_56 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_55, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec_ref(x_54);
x_60 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_61 = 1;
x_62 = l_Lean_Name_toString(x_59, x_61);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_63);
lean_ctor_set(x_2, 0, x_60);
x_64 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Std_Format_indentD(x_58);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_56, 0, x_67);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_ctor_get(x_54, 0);
lean_inc(x_69);
lean_dec_ref(x_54);
x_70 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_71 = 1;
x_72 = l_Lean_Name_toString(x_69, x_71);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_73);
lean_ctor_set(x_2, 0, x_70);
x_74 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Std_Format_indentD(x_68);
x_77 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_54);
return x_56;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_2);
x_81 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec_ref(x_79);
x_85 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__1));
x_86 = 1;
x_87 = l_Lean_Name_toString(x_84, x_86);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__3));
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Std_Format_indentD(x_82);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
else
{
lean_dec_ref(x_79);
return x_81;
}
}
}
default: 
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_95);
lean_dec_ref(x_2);
x_96 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_95, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
x_100 = l_Std_Format_indentD(x_98);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_96, 0, x_101);
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
lean_dec(x_96);
x_103 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppAlt___closed__5));
x_104 = l_Std_Format_indentD(x_102);
x_105 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
else
{
return x_96;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppAlt(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_12 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_13);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_13);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_dec(x_13);
lean_free_object(x_2);
return x_14;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_29 = l_Lean_Compiler_LCNF_PP_ppLetDecl(x_1, x_27, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(1);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_dec(x_30);
return x_31;
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_29;
}
}
}
case 1:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_43 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_41, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_42, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_44);
lean_ctor_set(x_2, 0, x_48);
x_49 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(1);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_45, 0, x_53);
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
lean_dec(x_45);
x_55 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_44);
lean_ctor_set(x_2, 0, x_55);
x_56 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_box(1);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
else
{
lean_dec(x_44);
lean_free_object(x_2);
return x_45;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_42);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_43;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_64 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_62, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_63, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(1);
x_74 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_dec(x_65);
return x_66;
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_64;
}
}
}
case 2:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_2, 0);
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_80 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_78, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_79, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_81);
lean_ctor_set(x_2, 0, x_85);
x_86 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(1);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set(x_82, 0, x_90);
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
lean_dec(x_82);
x_92 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_81);
lean_ctor_set(x_2, 0, x_92);
x_93 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_box(1);
x_96 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
else
{
lean_dec(x_81);
lean_free_object(x_2);
return x_82;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_79);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_80;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_101 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_99, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_100, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__5));
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
x_108 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_box(1);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
if (lean_is_scalar(x_105)) {
 x_113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_113 = x_105;
}
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_dec(x_102);
return x_103;
}
}
else
{
lean_dec_ref(x_100);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_101;
}
}
}
case 3:
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_2);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_2, 0);
x_116 = lean_ctor_get(x_2, 1);
x_117 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_115, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_116, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_116);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_118);
lean_ctor_set(x_2, 0, x_122);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_2);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_119, 0, x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
lean_dec(x_119);
x_125 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
lean_ctor_set_tag(x_2, 5);
lean_ctor_set(x_2, 1, x_118);
lean_ctor_set(x_2, 0, x_125);
x_126 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_126, 0, x_2);
lean_ctor_set(x_126, 1, x_124);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
else
{
lean_dec(x_118);
lean_free_object(x_2);
return x_119;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_116);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_117;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_2, 0);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_2);
x_130 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_128, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l_Lean_Compiler_LCNF_PP_ppArgs(x_1, x_129, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__7));
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_131);
x_137 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
else
{
lean_dec(x_131);
return x_132;
}
}
else
{
lean_dec_ref(x_129);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_130;
}
}
}
case 4:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_139);
lean_dec_ref(x_2);
x_140 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_139, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 3);
lean_inc_ref(x_142);
lean_dec_ref(x_139);
x_143 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_141, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
lean_inc_ref(x_3);
x_145 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_140, x_3, x_6, x_7);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_box(1);
x_148 = lean_box(x_1);
x_149 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppAlt___boxed), 8, 1);
lean_closure_set(x_149, 0, x_148);
x_150 = l___private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_prefixJoin___redArg(x_147, x_142, x_149, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_142);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_150, 0);
x_153 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
x_155 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_156 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_146);
x_158 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_150, 0, x_158);
return x_150;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_150, 0);
lean_inc(x_159);
lean_dec(x_150);
x_160 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__9));
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_144);
x_162 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_146);
x_165 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_159);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
else
{
lean_dec(x_146);
lean_dec(x_144);
return x_150;
}
}
else
{
lean_dec(x_144);
lean_dec_ref(x_142);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_145;
}
}
else
{
lean_dec_ref(x_142);
lean_dec_ref(x_140);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_143;
}
}
case 5:
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_3);
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
lean_dec_ref(x_2);
x_168 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_167, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
x_172 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_168, 0, x_172);
return x_168;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_168, 0);
lean_inc(x_173);
lean_dec(x_168);
x_174 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__11));
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
else
{
return x_168;
}
}
case 6:
{
uint8_t x_177; 
lean_dec(x_5);
lean_dec_ref(x_4);
x_177 = !lean_is_exclusive(x_2);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_2, 0);
x_179 = lean_ctor_get(x_6, 2);
x_180 = l_Lean_pp_all;
x_181 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec_ref(x_178);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_182 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_182);
return x_2;
}
else
{
lean_object* x_183; 
lean_free_object(x_2);
x_183 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_178, x_3, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_183, 0, x_187);
return x_183;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
lean_dec(x_183);
x_189 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
else
{
return x_183;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
lean_dec(x_2);
x_193 = lean_ctor_get(x_6, 2);
x_194 = l_Lean_pp_all;
x_195 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_193, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_192);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
x_196 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__13));
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
else
{
lean_object* x_198; 
x_198 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_192, x_3, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__15));
x_202 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
if (lean_is_scalar(x_200)) {
 x_203 = lean_alloc_ctor(0, 1, 0);
} else {
 x_203 = x_200;
}
lean_ctor_set(x_203, 0, x_202);
return x_203;
}
else
{
return x_198;
}
}
}
}
case 7:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_2, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_2, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_207);
lean_dec_ref(x_2);
x_208 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_204, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_206, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_207, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
x_217 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_209);
x_218 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Nat_reprFast(x_205);
lean_ctor_set_tag(x_210, 3);
lean_ctor_set(x_210, 0, x_220);
x_221 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_210);
x_222 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_223 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_212);
x_225 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_226 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_228 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_box(1);
x_230 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_215);
lean_ctor_set(x_213, 0, x_231);
return x_213;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_232 = lean_ctor_get(x_213, 0);
lean_inc(x_232);
lean_dec(x_213);
x_233 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
x_234 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_209);
x_235 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_236 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Nat_reprFast(x_205);
lean_ctor_set_tag(x_210, 3);
lean_ctor_set(x_210, 0, x_237);
x_238 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_210);
x_239 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_212);
x_242 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_245 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_box(1);
x_247 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_232);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
else
{
lean_free_object(x_210);
lean_dec(x_212);
lean_dec(x_209);
lean_dec(x_205);
return x_213;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_210, 0);
lean_inc(x_250);
lean_dec(x_210);
x_251 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_207, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__17));
x_255 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_209);
x_256 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_257 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Nat_reprFast(x_205);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_259);
x_261 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_262 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_250);
x_264 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_265 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_267 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_box(1);
x_269 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_252);
if (lean_is_scalar(x_253)) {
 x_271 = lean_alloc_ctor(0, 1, 0);
} else {
 x_271 = x_253;
}
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
else
{
lean_dec(x_250);
lean_dec(x_209);
lean_dec(x_205);
return x_251;
}
}
}
else
{
lean_dec(x_209);
lean_dec_ref(x_207);
lean_dec(x_205);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_210;
}
}
else
{
lean_dec_ref(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_208;
}
}
default: 
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_272 = lean_ctor_get(x_2, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_2, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_2, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_2, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_276);
x_277 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_277);
lean_dec_ref(x_2);
x_278 = lean_ctor_get(x_6, 2);
x_279 = l_Lean_pp_letVarTypes;
x_280 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_278, x_279);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec_ref(x_276);
x_281 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_272, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 0);
x_284 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_275, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_287) == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_289 = lean_ctor_get(x_287, 0);
x_290 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_291 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_283);
x_292 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_293 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = l_Nat_reprFast(x_273);
lean_ctor_set_tag(x_284, 3);
lean_ctor_set(x_284, 0, x_294);
x_295 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_284);
x_296 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_297 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_281, 3);
lean_ctor_set(x_281, 0, x_298);
x_299 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_281);
x_300 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_301 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_286);
x_303 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_304 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_306 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_box(1);
x_308 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_289);
lean_ctor_set(x_287, 0, x_309);
return x_287;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_310 = lean_ctor_get(x_287, 0);
lean_inc(x_310);
lean_dec(x_287);
x_311 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_312 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_283);
x_313 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_314 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Nat_reprFast(x_273);
lean_ctor_set_tag(x_284, 3);
lean_ctor_set(x_284, 0, x_315);
x_316 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_284);
x_317 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_318 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_281, 3);
lean_ctor_set(x_281, 0, x_319);
x_320 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_281);
x_321 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_322 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_286);
x_324 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_325 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_327 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_box(1);
x_329 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_310);
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_330);
return x_331;
}
}
else
{
lean_free_object(x_284);
lean_dec(x_286);
lean_free_object(x_281);
lean_dec(x_283);
lean_dec(x_274);
lean_dec(x_273);
return x_287;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_284, 0);
lean_inc(x_332);
lean_dec(x_284);
x_333 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
x_336 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_337 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_283);
x_338 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_339 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Nat_reprFast(x_273);
x_341 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_341, 0, x_340);
x_342 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_341);
x_343 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_344 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_281, 3);
lean_ctor_set(x_281, 0, x_345);
x_346 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_281);
x_347 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_348 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_332);
x_350 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_351 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_353 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_box(1);
x_355 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_334);
if (lean_is_scalar(x_335)) {
 x_357 = lean_alloc_ctor(0, 1, 0);
} else {
 x_357 = x_335;
}
lean_ctor_set(x_357, 0, x_356);
return x_357;
}
else
{
lean_dec(x_332);
lean_free_object(x_281);
lean_dec(x_283);
lean_dec(x_274);
lean_dec(x_273);
return x_333;
}
}
}
else
{
lean_free_object(x_281);
lean_dec(x_283);
lean_dec_ref(x_277);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_284;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_281, 0);
lean_inc(x_358);
lean_dec(x_281);
x_359 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_275, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
x_362 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
x_365 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_366 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_358);
x_367 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_368 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = l_Nat_reprFast(x_273);
if (lean_is_scalar(x_361)) {
 x_370 = lean_alloc_ctor(3, 1, 0);
} else {
 x_370 = x_361;
 lean_ctor_set_tag(x_370, 3);
}
lean_ctor_set(x_370, 0, x_369);
x_371 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_370);
x_372 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_373 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_Nat_reprFast(x_274);
x_375 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_375);
x_377 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__21));
x_378 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_360);
x_380 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_381 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_382 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_383 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_box(1);
x_385 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_363);
if (lean_is_scalar(x_364)) {
 x_387 = lean_alloc_ctor(0, 1, 0);
} else {
 x_387 = x_364;
}
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
else
{
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_358);
lean_dec(x_274);
lean_dec(x_273);
return x_362;
}
}
else
{
lean_dec(x_358);
lean_dec_ref(x_277);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_359;
}
}
}
else
{
lean_dec_ref(x_277);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_281;
}
}
else
{
lean_object* x_388; 
x_388 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_272, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec_ref(x_388);
lean_inc_ref(x_3);
x_390 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_276, x_3, x_6, x_7);
if (lean_obj_tag(x_390) == 0)
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_390, 0);
x_393 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_275, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_393, 0);
x_396 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_396) == 0)
{
uint8_t x_397; 
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_400 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_389);
x_401 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_402 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Nat_reprFast(x_273);
lean_ctor_set_tag(x_393, 3);
lean_ctor_set(x_393, 0, x_403);
x_404 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_393);
x_405 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_406 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_390, 3);
lean_ctor_set(x_390, 0, x_407);
x_408 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_390);
x_409 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
x_410 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_392);
x_412 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_413 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_395);
x_415 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_416 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_418 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = lean_box(1);
x_420 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_398);
lean_ctor_set(x_396, 0, x_421);
return x_396;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_422 = lean_ctor_get(x_396, 0);
lean_inc(x_422);
lean_dec(x_396);
x_423 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_424 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_389);
x_425 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_426 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = l_Nat_reprFast(x_273);
lean_ctor_set_tag(x_393, 3);
lean_ctor_set(x_393, 0, x_427);
x_428 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_393);
x_429 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_430 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
x_431 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_390, 3);
lean_ctor_set(x_390, 0, x_431);
x_432 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_390);
x_433 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
x_434 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
x_435 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_392);
x_436 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_437 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_395);
x_439 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_440 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_442 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
x_443 = lean_box(1);
x_444 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_422);
x_446 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_446, 0, x_445);
return x_446;
}
}
else
{
lean_free_object(x_393);
lean_dec(x_395);
lean_free_object(x_390);
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_274);
lean_dec(x_273);
return x_396;
}
}
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_393, 0);
lean_inc(x_447);
lean_dec(x_393);
x_448 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
x_451 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_452 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_389);
x_453 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_454 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Nat_reprFast(x_273);
x_456 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_456, 0, x_455);
x_457 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_456);
x_458 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_459 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
x_460 = l_Nat_reprFast(x_274);
lean_ctor_set_tag(x_390, 3);
lean_ctor_set(x_390, 0, x_460);
x_461 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_390);
x_462 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
x_463 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_392);
x_465 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_466 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_447);
x_468 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_469 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_471 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_box(1);
x_473 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
x_474 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_449);
if (lean_is_scalar(x_450)) {
 x_475 = lean_alloc_ctor(0, 1, 0);
} else {
 x_475 = x_450;
}
lean_ctor_set(x_475, 0, x_474);
return x_475;
}
else
{
lean_dec(x_447);
lean_free_object(x_390);
lean_dec(x_392);
lean_dec(x_389);
lean_dec(x_274);
lean_dec(x_273);
return x_448;
}
}
}
else
{
lean_free_object(x_390);
lean_dec(x_392);
lean_dec(x_389);
lean_dec_ref(x_277);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_393;
}
}
else
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_ctor_get(x_390, 0);
lean_inc(x_476);
lean_dec(x_390);
x_477 = l_Lean_Compiler_LCNF_PP_ppFVar___redArg(x_275, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 x_479 = x_477;
} else {
 lean_dec_ref(x_477);
 x_479 = lean_box(0);
}
x_480 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_277, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
x_483 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__23));
x_484 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_389);
x_485 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__19));
x_486 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
x_487 = l_Nat_reprFast(x_273);
if (lean_is_scalar(x_479)) {
 x_488 = lean_alloc_ctor(3, 1, 0);
} else {
 x_488 = x_479;
 lean_ctor_set_tag(x_488, 3);
}
lean_ctor_set(x_488, 0, x_487);
x_489 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_489, 0, x_486);
lean_ctor_set(x_489, 1, x_488);
x_490 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetValue___closed__11));
x_491 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Nat_reprFast(x_274);
x_493 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_493, 0, x_492);
x_494 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_493);
x_495 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__25));
x_496 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_476);
x_498 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppLetDecl___closed__3));
x_499 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_478);
x_501 = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_PrettyPrinter_0__Lean_Compiler_LCNF_PP_join_spec__0___redArg___closed__1));
x_502 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
x_503 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__1));
x_504 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_box(1);
x_506 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_481);
if (lean_is_scalar(x_482)) {
 x_508 = lean_alloc_ctor(0, 1, 0);
} else {
 x_508 = x_482;
}
lean_ctor_set(x_508, 0, x_507);
return x_508;
}
else
{
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_476);
lean_dec(x_389);
lean_dec(x_274);
lean_dec(x_273);
return x_480;
}
}
else
{
lean_dec(x_476);
lean_dec(x_389);
lean_dec_ref(x_277);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_477;
}
}
}
else
{
lean_dec(x_389);
lean_dec_ref(x_277);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_390;
}
}
else
{
lean_dec_ref(x_277);
lean_dec_ref(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_388;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Compiler_LCNF_PP_getFunType(x_1, x_10, x_11, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_3);
x_17 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_16, x_3, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = 1;
x_24 = l_Lean_Name_toString(x_9, x_23);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_24);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_14);
x_26 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_29 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_Format_indentD(x_22);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = 1;
x_35 = l_Lean_Name_toString(x_9, x_34);
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 0, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_14);
x_37 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_19);
x_40 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Format_indentD(x_33);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_free_object(x_17);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
return x_20;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = 1;
x_50 = l_Lean_Name_toString(x_9, x_49);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
x_53 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
x_56 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_Format_indentD(x_47);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_48)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_48;
}
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
lean_dec(x_45);
lean_dec(x_14);
lean_dec(x_9);
return x_46;
}
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_17;
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_61 = !lean_is_exclusive(x_15);
if (x_61 == 0)
{
return x_15;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_15, 0);
lean_inc(x_62);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppCode(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = l_Lean_Compiler_LCNF_PP_ppCode(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppDeclValue___closed__1));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_ppDeclValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_7, x_5);
if (x_6 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1));
x_10 = l_Lean_Name_isPrefixOf(x_9, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_10);
return x_1;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_13, 0, x_3);
lean_inc(x_2);
x_14 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(x_2, x_13, x_11);
if (x_12 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___closed__1));
x_16 = l_Lean_Name_isPrefixOf(x_15, x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0_spec__0(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_run___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_PP_run___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_71; uint8_t x_92; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_pp_sanitizeNames;
x_11 = 0;
lean_inc_ref(x_8);
x_12 = l_Lean_Option_set___at___00Lean_Compiler_LCNF_PP_run_spec__0(x_8, x_10, x_11);
x_13 = l_Lean_diagnostics;
x_14 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_ppArg_spec__0(x_12, x_13);
x_92 = l_Lean_Kernel_isDiagnosticsEnabled(x_9);
lean_dec_ref(x_9);
if (x_92 == 0)
{
if (x_14 == 0)
{
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_70;
}
else
{
x_71 = x_92;
goto block_91;
}
}
else
{
x_71 = x_14;
goto block_91;
}
block_70:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_st_ref_get(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 3);
x_23 = lean_ctor_get(x_15, 5);
x_24 = lean_ctor_get(x_15, 6);
x_25 = lean_ctor_get(x_15, 7);
x_26 = lean_ctor_get(x_15, 8);
x_27 = lean_ctor_get(x_15, 9);
x_28 = lean_ctor_get(x_15, 10);
x_29 = lean_ctor_get(x_15, 11);
x_30 = lean_ctor_get(x_15, 12);
x_31 = lean_ctor_get(x_15, 13);
x_32 = lean_ctor_get(x_15, 4);
lean_dec(x_32);
x_33 = lean_ctor_get(x_15, 2);
lean_dec(x_33);
x_34 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_36);
lean_dec(x_18);
x_37 = l_Lean_maxRecDepth;
x_38 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(x_12, x_37);
lean_ctor_set(x_15, 4, x_38);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*14, x_14);
x_39 = lean_unbox(x_35);
lean_dec(x_35);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_36, x_39);
lean_dec_ref(x_36);
x_41 = lean_apply_6(x_1, x_40, x_2, x_3, x_15, x_16, lean_box(0));
return x_41;
}
else
{
uint8_t x_42; 
lean_free_object(x_15);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_12);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
x_47 = lean_ctor_get(x_15, 3);
x_48 = lean_ctor_get(x_15, 5);
x_49 = lean_ctor_get(x_15, 6);
x_50 = lean_ctor_get(x_15, 7);
x_51 = lean_ctor_get(x_15, 8);
x_52 = lean_ctor_get(x_15, 9);
x_53 = lean_ctor_get(x_15, 10);
x_54 = lean_ctor_get(x_15, 11);
x_55 = lean_ctor_get(x_15, 12);
x_56 = lean_ctor_get_uint8(x_15, sizeof(void*)*14 + 1);
x_57 = lean_ctor_get(x_15, 13);
lean_inc(x_57);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_58 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_60);
lean_dec(x_18);
x_61 = l_Lean_maxRecDepth;
x_62 = l_Lean_Option_get___at___00Lean_Compiler_LCNF_PP_run_spec__1(x_12, x_61);
x_63 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_63, 0, x_45);
lean_ctor_set(x_63, 1, x_46);
lean_ctor_set(x_63, 2, x_12);
lean_ctor_set(x_63, 3, x_47);
lean_ctor_set(x_63, 4, x_62);
lean_ctor_set(x_63, 5, x_48);
lean_ctor_set(x_63, 6, x_49);
lean_ctor_set(x_63, 7, x_50);
lean_ctor_set(x_63, 8, x_51);
lean_ctor_set(x_63, 9, x_52);
lean_ctor_set(x_63, 10, x_53);
lean_ctor_set(x_63, 11, x_54);
lean_ctor_set(x_63, 12, x_55);
lean_ctor_set(x_63, 13, x_57);
lean_ctor_set_uint8(x_63, sizeof(void*)*14, x_14);
lean_ctor_set_uint8(x_63, sizeof(void*)*14 + 1, x_56);
x_64 = lean_unbox(x_59);
lean_dec(x_59);
x_65 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_60, x_64);
lean_dec_ref(x_60);
x_66 = lean_apply_6(x_1, x_65, x_2, x_3, x_63, x_16, lean_box(0));
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_12);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
block_91:
{
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_st_ref_take(x_5);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 5);
lean_dec(x_75);
x_76 = l_Lean_Kernel_enableDiag(x_74, x_14);
x_77 = l_Lean_Compiler_LCNF_PP_run___redArg___closed__2;
lean_ctor_set(x_72, 5, x_77);
lean_ctor_set(x_72, 0, x_76);
x_78 = lean_st_ref_set(x_5, x_72);
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
x_81 = lean_ctor_get(x_72, 2);
x_82 = lean_ctor_get(x_72, 3);
x_83 = lean_ctor_get(x_72, 4);
x_84 = lean_ctor_get(x_72, 6);
x_85 = lean_ctor_get(x_72, 7);
x_86 = lean_ctor_get(x_72, 8);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
x_87 = l_Lean_Kernel_enableDiag(x_79, x_14);
x_88 = l_Lean_Compiler_LCNF_PP_run___redArg___closed__2;
x_89 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_80);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_82);
lean_ctor_set(x_89, 4, x_83);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set(x_89, 6, x_84);
lean_ctor_set(x_89, 7, x_85);
lean_ctor_set(x_89, 8, x_86);
x_90 = lean_st_ref_set(x_5, x_89);
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_70;
}
}
else
{
x_15 = x_4;
x_16 = x_5;
x_17 = lean_box(0);
goto block_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_PP_run___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_run___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_PP_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_PP_run(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppCode___boxed), 8, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Compiler_LCNF_PP_run___redArg(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_ppCode(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PP_ppLetValue___boxed), 8, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Compiler_LCNF_PP_run___redArg(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_ppLetValue(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_12 = l_Lean_Compiler_LCNF_PP_ppParams(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Compiler_LCNF_PP_getFunType(x_1, x_2, x_3, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_6);
x_16 = l_Lean_Compiler_LCNF_PP_ppExpr___redArg(x_15, x_6, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_1, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
x_23 = 1;
x_24 = l_Lean_Name_toString(x_5, x_23);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_30 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Std_Format_indentD(x_21);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
x_36 = 1;
x_37 = l_Lean_Name_toString(x_5, x_36);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_37);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_16);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
x_40 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_18);
x_43 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Std_Format_indentD(x_34);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
else
{
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_5);
return x_19;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_16, 0);
lean_inc(x_48);
lean_dec(x_16);
x_49 = l_Lean_Compiler_LCNF_PP_ppDeclValue(x_1, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = ((lean_object*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___closed__1));
x_53 = 1;
x_54 = l_Lean_Name_toString(x_5, x_53);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_13);
x_58 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppParam___redArg___closed__1));
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
x_61 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppFunDecl___closed__1));
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Std_Format_indentD(x_50);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_51)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_51;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_5);
return x_49;
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_16;
}
}
else
{
uint8_t x_66; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_66 = !lean_is_exclusive(x_14);
if (x_66 == 0)
{
return x_14;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_14, 0);
lean_inc(x_67);
lean_dec(x_14);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_Lean_Compiler_LCNF_ppDecl___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_8);
x_13 = lean_box(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl___lam__0___boxed), 11, 5);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_11);
lean_closure_set(x_14, 3, x_9);
lean_closure_set(x_14, 4, x_10);
x_15 = l_Lean_Compiler_LCNF_PP_run___redArg(x_14, x_3, x_4, x_5, x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_ppDecl(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_PP_ppFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = ((lean_object*)(l_Lean_Compiler_LCNF_PP_ppCode___closed__3));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_ppFunDecl___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppFunDecl___lam__0___boxed), 8, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Compiler_LCNF_PP_run___redArg(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l_Lean_Compiler_LCNF_ppFunDecl(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_st_ref_set(x_1, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_get(x_4);
x_7 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3;
lean_inc(x_4);
x_8 = l_Lean_Compiler_LCNF_CompilerM_run___redArg(x_2, x_7, x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_ctor_set_tag(x_8, 1);
x_11 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_4, x_6, x_8);
lean_dec_ref(x_8);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_inc(x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_4, x_6, x_16);
lean_dec_ref(x_16);
lean_dec(x_4);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_18 = x_17;
} else {
 lean_dec_ref(x_17);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec_ref(x_8);
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___lam__0(x_4, x_6, x_21);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
x_7 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_ppDecl_x27___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1;
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppDecl_x27___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_3, x_9, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Compiler_LCNF_ppDecl_x27(x_7, x_2, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Compiler_LCNF_Code_internalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_ppCode(x_1, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Compiler_LCNF_ppCode_x27___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1;
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ppCode_x27___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg(x_3, x_9, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ppCode_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_Compiler_LCNF_ppCode_x27(x_7, x_2, x_8, x_4, x_5);
return x_9;
}
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__0);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__1);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__2);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__3);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__4);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__5);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__6);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__7);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__8);
l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9 = _init_l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppExpr___redArg___closed__9);
l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6 = _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__6);
l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7 = _init_l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_ppArg___redArg___closed__7);
l_Lean_Compiler_LCNF_PP_run___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_run___redArg___closed__0);
l_Lean_Compiler_LCNF_PP_run___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_run___redArg___closed__1);
l_Lean_Compiler_LCNF_PP_run___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_PP_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_PP_run___redArg___closed__2);
l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__0);
l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__1);
l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__2);
l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_runCompilerWithoutModifyingState___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
