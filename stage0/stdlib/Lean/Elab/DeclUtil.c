// Lean compiler output
// Module: Lean.Elab.DeclUtil
// Imports: public import Lean.Meta.Check public import Lean.Parser.Command
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "Internal error: Mismatched number of parameters when checking type compatibility"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Parameter `"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Parameter names `"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "` and `"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "` differ but were expected to match"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Binder annotations for parameter `"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14;
static const lean_string_object l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` must match"};
static const lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_sortDeclLevelParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_sortDeclLevelParams___closed__0 = (const lean_object*)&l_Lean_Elab_sortDeclLevelParams___closed__0_value;
static const lean_string_object l_Lean_Elab_sortDeclLevelParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unused universe parameter '"};
static const lean_object* l_Lean_Elab_sortDeclLevelParams___closed__1 = (const lean_object*)&l_Lean_Elab_sortDeclLevelParams___closed__1_value;
static const lean_string_object l_Lean_Elab_sortDeclLevelParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_sortDeclLevelParams___closed__2 = (const lean_object*)&l_Lean_Elab_sortDeclLevelParams___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
v___x_8_ = lean_apply_6(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_9_, lean_object* v_b_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(v_k_9_, v_b_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
lean_dec(v___y_12_);
lean_dec_ref(v___y_11_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(lean_object* v_name_17_, uint8_t v_bi_18_, lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_kind_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_17_, v_bi_18_, v_type_19_, v___f_27_, v_kind_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v___x_28_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_a_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_a_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_28_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_28_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___boxed(lean_object* v_name_45_, lean_object* v_bi_46_, lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_kind_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_bi_boxed_55_; uint8_t v_kind_boxed_56_; lean_object* v_res_57_; 
v_bi_boxed_55_ = lean_unbox(v_bi_46_);
v_kind_boxed_56_ = lean_unbox(v_kind_49_);
v_res_57_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_name_45_, v_bi_boxed_55_, v_type_47_, v_k_48_, v_kind_boxed_56_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(lean_object* v_00_u03b1_58_, lean_object* v_name_59_, uint8_t v_bi_60_, lean_object* v_type_61_, lean_object* v_k_62_, uint8_t v_kind_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_name_59_, v_bi_60_, v_type_61_, v_k_62_, v_kind_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___boxed(lean_object* v_00_u03b1_70_, lean_object* v_name_71_, lean_object* v_bi_72_, lean_object* v_type_73_, lean_object* v_k_74_, lean_object* v_kind_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_bi_boxed_81_; uint8_t v_kind_boxed_82_; lean_object* v_res_83_; 
v_bi_boxed_81_ = lean_unbox(v_bi_72_);
v_kind_boxed_82_ = lean_unbox(v_kind_75_);
v_res_83_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(v_00_u03b1_70_, v_name_71_, v_bi_boxed_81_, v_type_73_, v_k_74_, v_kind_boxed_82_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(lean_object* v_msgData_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_env_91_; lean_object* v___x_92_; lean_object* v_mctx_93_; lean_object* v_lctx_94_; lean_object* v_options_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_env_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_env_91_);
lean_dec(v___x_90_);
v___x_92_ = lean_st_ref_get(v___y_86_);
v_mctx_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_mctx_93_);
lean_dec(v___x_92_);
v_lctx_94_ = lean_ctor_get(v___y_85_, 2);
v_options_95_ = lean_ctor_get(v___y_87_, 2);
lean_inc_ref(v_options_95_);
lean_inc_ref(v_lctx_94_);
v___x_96_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_96_, 0, v_env_91_);
lean_ctor_set(v___x_96_, 1, v_mctx_93_);
lean_ctor_set(v___x_96_, 2, v_lctx_94_);
lean_ctor_set(v___x_96_, 3, v_options_95_);
v___x_97_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_msgData_84_);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_ref_112_; lean_object* v___x_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_ref_112_ = lean_ctor_get(v___y_109_, 5);
v___x_113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msg_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_inc(v_ref_112_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_ref_112_);
lean_ctor_set(v___x_118_, 1, v_a_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
lean_ctor_set(v___x_116_, 0, v___x_118_);
v___x_120_ = v___x_116_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0));
v___x_132_ = l_Lean_stringToMessageData(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(lean_object* v_body_133_, lean_object* v_body_134_, lean_object* v_x_135_, lean_object* v_k_136_, lean_object* v_n_137_, lean_object* v_x_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(v_body_133_, v_body_134_, v_x_135_, v_k_136_, v_n_137_, v_x_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v_n_137_);
lean_dec_ref(v_body_134_);
lean_dec_ref(v_body_133_);
return v_res_144_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3));
v___x_149_ = l_Lean_stringToMessageData(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5));
v___x_152_ = l_Lean_stringToMessageData(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg(lean_object* v_k_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_zero_178_; uint8_t v_isZero_179_; 
v_zero_178_ = lean_unsigned_to_nat(0u);
v_isZero_179_ = lean_nat_dec_eq(v_x_169_, v_zero_178_);
if (v_isZero_179_ == 1)
{
lean_object* v___x_180_; 
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
v___x_180_ = lean_apply_8(v_k_168_, v_x_172_, v_x_170_, v_x_171_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, lean_box(0));
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
v___x_181_ = lean_whnf(v_x_170_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref(v___x_181_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
v___x_183_ = lean_whnf(v_x_171_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref(v___x_183_);
if (lean_obj_tag(v_a_182_) == 7)
{
if (lean_obj_tag(v_a_184_) == 7)
{
lean_object* v_binderName_192_; lean_object* v_binderType_193_; lean_object* v_body_194_; uint8_t v_binderInfo_195_; lean_object* v_binderName_196_; lean_object* v_binderType_197_; lean_object* v_body_198_; uint8_t v_binderInfo_199_; lean_object* v_one_200_; lean_object* v_n_201_; lean_object* v___f_202_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_280_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; uint8_t v___y_284_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; uint8_t v___x_300_; 
v_binderName_192_ = lean_ctor_get(v_a_182_, 0);
lean_inc(v_binderName_192_);
v_binderType_193_ = lean_ctor_get(v_a_182_, 1);
lean_inc_ref(v_binderType_193_);
v_body_194_ = lean_ctor_get(v_a_182_, 2);
lean_inc_ref(v_body_194_);
v_binderInfo_195_ = lean_ctor_get_uint8(v_a_182_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_182_);
v_binderName_196_ = lean_ctor_get(v_a_184_, 0);
lean_inc(v_binderName_196_);
v_binderType_197_ = lean_ctor_get(v_a_184_, 1);
lean_inc_ref(v_binderType_197_);
v_body_198_ = lean_ctor_get(v_a_184_, 2);
lean_inc_ref(v_body_198_);
v_binderInfo_199_ = lean_ctor_get_uint8(v_a_184_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_184_);
v_one_200_ = lean_unsigned_to_nat(1u);
v_n_201_ = lean_nat_sub(v_x_169_, v_one_200_);
v___f_202_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_202_, 0, v_body_194_);
lean_closure_set(v___f_202_, 1, v_body_198_);
lean_closure_set(v___f_202_, 2, v_x_172_);
lean_closure_set(v___f_202_, 3, v_k_168_);
lean_closure_set(v___f_202_, 4, v_n_201_);
v___x_300_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_195_, v_binderInfo_199_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v___f_202_);
lean_dec_ref(v_binderType_197_);
lean_dec(v_binderName_196_);
lean_dec_ref(v_binderType_193_);
v___x_301_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
v___x_302_ = lean_mk_syntax_ident(v_binderName_192_);
v___x_303_ = l_Lean_MessageData_ofSyntax(v___x_302_);
v___x_304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
v___x_306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_306_, v_a_173_, v_a_174_, v_a_175_, v_a_176_);
v_a_308_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_307_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
v___y_293_ = v_a_173_;
v___y_294_ = v_a_174_;
v___y_295_ = v_a_175_;
v___y_296_ = v_a_176_;
goto v___jp_292_;
}
v___jp_203_:
{
uint8_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = 0;
v___x_209_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_binderName_192_, v_binderInfo_195_, v_binderType_193_, v___f_202_, v___x_208_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
return v___x_209_;
}
v___jp_210_:
{
lean_object* v___x_215_; 
lean_inc_ref(v_binderType_197_);
lean_inc_ref(v_binderType_193_);
v___x_215_ = l_Lean_Meta_isExprDefEq(v_binderType_193_, v_binderType_197_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; uint8_t v___x_217_; 
v_a_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref(v___x_215_);
v___x_217_ = lean_unbox(v_a_216_);
lean_dec(v_a_216_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec_ref(v___f_202_);
v___x_218_ = lean_box(0);
v___x_219_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_220_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_binderType_193_, v_binderType_197_, v___x_218_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref(v___x_220_);
v___x_222_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4);
v___x_223_ = lean_mk_syntax_ident(v_binderName_192_);
v___x_224_ = l_Lean_MessageData_ofSyntax(v___x_223_);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_222_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
lean_ctor_set(v___x_228_, 1, v_a_221_);
v___x_229_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_228_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
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
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_binderName_192_);
v_a_238_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_220_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_220_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_197_);
v___y_204_ = v___y_211_;
v___y_205_ = v___y_212_;
v___y_206_ = v___y_213_;
v___y_207_ = v___y_214_;
goto v___jp_203_;
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v___f_202_);
lean_dec_ref(v_binderType_197_);
lean_dec_ref(v_binderType_193_);
lean_dec(v_binderName_192_);
v_a_246_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_215_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_215_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
v___jp_254_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v___x_259_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8);
v___x_260_ = lean_mk_syntax_ident(v_binderName_192_);
v___x_261_ = l_Lean_MessageData_ofSyntax(v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_259_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_mk_syntax_ident(v_binderName_196_);
v___x_266_ = l_Lean_MessageData_ofSyntax(v___x_265_);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_269_, v___y_256_, v___y_257_, v___y_258_, v___y_255_);
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
v___jp_279_:
{
if (v___y_284_ == 0)
{
lean_dec_ref(v___f_202_);
lean_dec_ref(v_binderType_197_);
lean_dec_ref(v_binderType_193_);
v___y_255_ = v___y_281_;
v___y_256_ = v___y_280_;
v___y_257_ = v___y_282_;
v___y_258_ = v___y_283_;
goto v___jp_254_;
}
else
{
lean_dec(v_binderName_196_);
v___y_211_ = v___y_280_;
v___y_212_ = v___y_282_;
v___y_213_ = v___y_283_;
v___y_214_ = v___y_281_;
goto v___jp_210_;
}
}
v___jp_285_:
{
if (v___y_290_ == 0)
{
lean_dec_ref(v___f_202_);
lean_dec_ref(v_binderType_197_);
lean_dec_ref(v_binderType_193_);
v___y_255_ = v___y_287_;
v___y_256_ = v___y_286_;
v___y_257_ = v___y_288_;
v___y_258_ = v___y_289_;
goto v___jp_254_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = l_Lean_Name_hasMacroScopes(v_binderName_196_);
v___y_280_ = v___y_286_;
v___y_281_ = v___y_287_;
v___y_282_ = v___y_288_;
v___y_283_ = v___y_289_;
v___y_284_ = v___x_291_;
goto v___jp_279_;
}
}
v___jp_292_:
{
uint8_t v___x_297_; 
v___x_297_ = lean_name_eq(v_binderName_192_, v_binderName_196_);
if (v___x_297_ == 0)
{
uint8_t v___x_298_; 
v___x_298_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_195_);
if (v___x_298_ == 0)
{
v___y_286_ = v___y_293_;
v___y_287_ = v___y_296_;
v___y_288_ = v___y_294_;
v___y_289_ = v___y_295_;
v___y_290_ = v___x_298_;
goto v___jp_285_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Name_hasMacroScopes(v_binderName_192_);
v___y_286_ = v___y_293_;
v___y_287_ = v___y_296_;
v___y_288_ = v___y_294_;
v___y_289_ = v___y_295_;
v___y_290_ = v___x_299_;
goto v___jp_285_;
}
}
else
{
v___y_280_ = v___y_293_;
v___y_281_ = v___y_296_;
v___y_282_ = v___y_294_;
v___y_283_ = v___y_295_;
v___y_284_ = v___x_297_;
goto v___jp_279_;
}
}
}
else
{
lean_dec_ref(v_a_182_);
lean_dec(v_a_184_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_k_168_);
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
goto v___jp_185_;
}
}
else
{
lean_dec(v_a_184_);
lean_dec(v_a_182_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_k_168_);
v___y_186_ = v_a_173_;
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1);
v___x_191_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_190_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec(v_a_182_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_k_168_);
v_a_316_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_183_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_183_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec_ref(v_x_172_);
lean_dec_ref(v_x_171_);
lean_dec_ref(v_k_168_);
v_a_324_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_181_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_181_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object* v_body_332_, lean_object* v_body_333_, lean_object* v_x_334_, lean_object* v_k_335_, lean_object* v_n_336_, lean_object* v_x_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_expr_instantiate1(v_body_332_, v_x_337_);
v___x_344_ = lean_expr_instantiate1(v_body_333_, v_x_337_);
v___x_345_ = lean_array_push(v_x_334_, v_x_337_);
v___x_346_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_335_, v_n_336_, v___x_343_, v___x_344_, v___x_345_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object* v_k_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_347_, v_x_348_, v_x_349_, v_x_350_, v_x_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_x_348_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object* v_00_u03b1_358_, lean_object* v_k_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_359_, v_x_360_, v_x_361_, v_x_362_, v_x_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object* v_00_u03b1_370_, lean_object* v_k_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_forallTelescopeCompatibleAux(v_00_u03b1_370_, v_k_371_, v_x_372_, v_x_373_, v_x_374_, v_x_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_x_372_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object* v_00_u03b1_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(v_00_u03b1_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object* v_k_398_, lean_object* v_runInBase_399_, lean_object* v_xs_400_, lean_object* v_type_u2081_401_, lean_object* v_type_u2082_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_apply_3(v_k_398_, v_xs_400_, v_type_u2081_401_, v_type_u2082_402_);
lean_inc(v___y_406_);
lean_inc_ref(v___y_405_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
v___x_409_ = lean_apply_7(v_runInBase_399_, lean_box(0), v___x_408_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, lean_box(0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object* v_k_410_, lean_object* v_runInBase_411_, lean_object* v_xs_412_, lean_object* v_type_u2081_413_, lean_object* v_type_u2082_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_410_, v_runInBase_411_, v_xs_412_, v_type_u2081_413_, v_type_u2082_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object* v_k_421_, lean_object* v_numParams_422_, lean_object* v_type_u2081_423_, lean_object* v_type_u2082_424_, lean_object* v_runInBase_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___f_431_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_431_, 0, v_k_421_);
lean_closure_set(v___f_431_, 1, v_runInBase_425_);
v___x_432_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_433_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v___f_431_, v_numParams_422_, v_type_u2081_423_, v_type_u2082_424_, v___x_432_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object* v_k_434_, lean_object* v_numParams_435_, lean_object* v_type_u2081_436_, lean_object* v_type_u2082_437_, lean_object* v_runInBase_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_434_, v_numParams_435_, v_type_u2081_436_, v_type_u2082_437_, v_runInBase_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v_numParams_435_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_type_u2081_447_, lean_object* v_type_u2082_448_, lean_object* v_numParams_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_toBind_451_; lean_object* v_liftWith_452_; lean_object* v_restoreM_453_; lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_toBind_451_ = lean_ctor_get(v_inst_445_, 1);
lean_inc(v_toBind_451_);
lean_dec_ref(v_inst_445_);
v_liftWith_452_ = lean_ctor_get(v_inst_446_, 0);
lean_inc(v_liftWith_452_);
v_restoreM_453_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_restoreM_453_);
lean_dec_ref(v_inst_446_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_454_, 0, v_k_450_);
lean_closure_set(v___f_454_, 1, v_numParams_449_);
lean_closure_set(v___f_454_, 2, v_type_u2081_447_);
lean_closure_set(v___f_454_, 3, v_type_u2082_448_);
v___x_455_ = lean_apply_2(v_liftWith_452_, lean_box(0), v___f_454_);
v___x_456_ = lean_apply_1(v_restoreM_453_, lean_box(0));
v___x_457_ = lean_apply_4(v_toBind_451_, lean_box(0), lean_box(0), v___x_455_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object* v_m_458_, lean_object* v_00_u03b1_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_type_u2081_462_, lean_object* v_type_u2082_463_, lean_object* v_numParams_464_, lean_object* v_k_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_forallTelescopeCompatible___redArg(v_inst_460_, v_inst_461_, v_type_u2081_462_, v_type_u2082_463_, v_numParams_464_, v_k_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object* v_stx_467_){
_start:
{
lean_object* v___x_468_; lean_object* v_binders_469_; lean_object* v___x_470_; lean_object* v_optType_471_; uint8_t v___x_472_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v_binders_469_ = l_Lean_Syntax_getArg(v_stx_467_, v___x_468_);
v___x_470_ = lean_unsigned_to_nat(1u);
v_optType_471_ = l_Lean_Syntax_getArg(v_stx_467_, v___x_470_);
v___x_472_ = l_Lean_Syntax_isNone(v_optType_471_);
if (v___x_472_ == 0)
{
lean_object* v_typeSpec_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_typeSpec_473_ = l_Lean_Syntax_getArg(v_optType_471_, v___x_468_);
lean_dec(v_optType_471_);
v___x_474_ = l_Lean_Syntax_getArg(v_typeSpec_473_, v___x_470_);
lean_dec(v_typeSpec_473_);
v___x_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v_binders_469_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_optType_471_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_binders_469_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object* v_stx_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Elab_expandOptDeclSig(v_stx_479_);
lean_dec(v_stx_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object* v_stx_481_){
_start:
{
lean_object* v___x_482_; lean_object* v_binders_483_; lean_object* v___x_484_; lean_object* v_typeSpec_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v_binders_483_ = l_Lean_Syntax_getArg(v_stx_481_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(1u);
v_typeSpec_485_ = l_Lean_Syntax_getArg(v_stx_481_, v___x_484_);
v___x_486_ = l_Lean_Syntax_getArg(v_typeSpec_485_, v___x_484_);
lean_dec(v_typeSpec_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_binders_483_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object* v_stx_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Elab_expandDeclSig(v_stx_488_);
lean_dec(v_stx_488_);
return v_res_489_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object* v_a_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
uint8_t v___x_492_; 
v___x_492_ = 0;
return v___x_492_;
}
else
{
lean_object* v_head_493_; lean_object* v_tail_494_; uint8_t v___x_495_; 
v_head_493_ = lean_ctor_get(v_x_491_, 0);
v_tail_494_ = lean_ctor_get(v_x_491_, 1);
v___x_495_ = lean_name_eq(v_a_490_, v_head_493_);
if (v___x_495_ == 0)
{
v_x_491_ = v_tail_494_;
goto _start;
}
else
{
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object* v_a_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_497_, v_x_498_);
lean_dec(v_x_498_);
lean_dec(v_a_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object* v_allUserParams_501_, lean_object* v_as_502_, size_t v_i_503_, size_t v_stop_504_, lean_object* v_b_505_){
_start:
{
lean_object* v___y_507_; uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_503_, v_stop_504_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_502_, v_i_503_);
v___x_513_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v___x_512_, v_allUserParams_501_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_inc(v___x_512_);
v___x_514_ = lean_array_push(v_b_505_, v___x_512_);
v___y_507_ = v___x_514_;
goto v___jp_506_;
}
else
{
v___y_507_ = v_b_505_;
goto v___jp_506_;
}
}
else
{
return v_b_505_;
}
v___jp_506_:
{
size_t v___x_508_; size_t v___x_509_; 
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_add(v_i_503_, v___x_508_);
v_i_503_ = v___x_509_;
v_b_505_ = v___y_507_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object* v_allUserParams_515_, lean_object* v_as_516_, lean_object* v_i_517_, lean_object* v_stop_518_, lean_object* v_b_519_){
_start:
{
size_t v_i_boxed_520_; size_t v_stop_boxed_521_; lean_object* v_res_522_; 
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_stop_boxed_521_ = lean_unbox_usize(v_stop_518_);
lean_dec(v_stop_518_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_515_, v_as_516_, v_i_boxed_520_, v_stop_boxed_521_, v_b_519_);
lean_dec_ref(v_as_516_);
lean_dec(v_allUserParams_515_);
return v_res_522_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object* v_a_523_, lean_object* v_as_524_, size_t v_i_525_, size_t v_stop_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_eq(v_i_525_, v_stop_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_array_uget_borrowed(v_as_524_, v_i_525_);
v___x_529_ = lean_name_eq(v_a_523_, v___x_528_);
if (v___x_529_ == 0)
{
size_t v___x_530_; size_t v___x_531_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_525_, v___x_530_);
v_i_525_ = v___x_531_;
goto _start;
}
else
{
return v___x_529_;
}
}
else
{
uint8_t v___x_533_; 
v___x_533_ = 0;
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object* v_a_534_, lean_object* v_as_535_, lean_object* v_i_536_, lean_object* v_stop_537_){
_start:
{
size_t v_i_boxed_538_; size_t v_stop_boxed_539_; uint8_t v_res_540_; lean_object* v_r_541_; 
v_i_boxed_538_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_stop_boxed_539_ = lean_unbox_usize(v_stop_537_);
lean_dec(v_stop_537_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_534_, v_as_535_, v_i_boxed_538_, v_stop_boxed_539_);
lean_dec_ref(v_as_535_);
lean_dec(v_a_534_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object* v_as_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v_as_542_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
return v___x_546_;
}
else
{
if (v___x_546_ == 0)
{
return v___x_546_;
}
else
{
size_t v___x_547_; size_t v___x_548_; uint8_t v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_545_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_543_, v_as_542_, v___x_547_, v___x_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object* v_as_550_, lean_object* v_a_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_as_550_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object* v_usedParams_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
if (lean_obj_tag(v_x_556_) == 0)
{
return v_x_555_;
}
else
{
lean_object* v_head_557_; lean_object* v_tail_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_head_557_ = lean_ctor_get(v_x_556_, 0);
v_tail_558_ = lean_ctor_get(v_x_556_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_x_556_);
if (v_isSharedCheck_568_ == 0)
{
v___x_560_ = v_x_556_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_tail_558_);
lean_inc(v_head_557_);
lean_dec(v_x_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; 
v___x_562_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_554_, v_head_557_);
if (v___x_562_ == 0)
{
lean_del_object(v___x_560_);
lean_dec(v_head_557_);
v_x_556_ = v_tail_558_;
goto _start;
}
else
{
lean_object* v___x_565_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_x_555_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_head_557_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_x_555_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
v_x_555_ = v___x_565_;
v_x_556_ = v_tail_558_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object* v_usedParams_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_569_, v_x_570_, v_x_571_);
lean_dec_ref(v_usedParams_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object* v_usedParams_573_, lean_object* v_scopeParams_574_, lean_object* v_x_575_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v_head_577_; lean_object* v_tail_578_; uint8_t v___x_579_; 
v_head_577_ = lean_ctor_get(v_x_575_, 0);
v_tail_578_ = lean_ctor_get(v_x_575_, 1);
v___x_579_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_573_, v_head_577_);
if (v___x_579_ == 0)
{
uint8_t v___x_580_; 
v___x_580_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_head_577_, v_scopeParams_574_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_inc(v_head_577_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v_head_577_);
return v___x_581_;
}
else
{
if (v___x_579_ == 0)
{
v_x_575_ = v_tail_578_;
goto _start;
}
else
{
lean_object* v___x_583_; 
lean_inc(v_head_577_);
v___x_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_583_, 0, v_head_577_);
return v___x_583_;
}
}
}
else
{
v_x_575_ = v_tail_578_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object* v_usedParams_585_, lean_object* v_scopeParams_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_585_, v_scopeParams_586_, v_x_587_);
lean_dec(v_x_587_);
lean_dec(v_scopeParams_586_);
lean_dec_ref(v_usedParams_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object* v_hi_589_, lean_object* v_pivot_590_, lean_object* v_as_591_, lean_object* v_i_592_, lean_object* v_k_593_){
_start:
{
uint8_t v___x_594_; 
v___x_594_ = lean_nat_dec_lt(v_k_593_, v_hi_589_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_k_593_);
v___x_595_ = lean_array_fswap(v_as_591_, v_i_592_, v_hi_589_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_i_592_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = lean_array_fget_borrowed(v_as_591_, v_k_593_);
v___x_598_ = l_Lean_Name_lt(v___x_597_, v_pivot_590_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_k_593_, v___x_599_);
lean_dec(v_k_593_);
v_k_593_ = v___x_600_;
goto _start;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_602_ = lean_array_fswap(v_as_591_, v_i_592_, v_k_593_);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_i_592_, v___x_603_);
lean_dec(v_i_592_);
v___x_605_ = lean_nat_add(v_k_593_, v___x_603_);
lean_dec(v_k_593_);
v_as_591_ = v___x_602_;
v_i_592_ = v___x_604_;
v_k_593_ = v___x_605_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object* v_hi_607_, lean_object* v_pivot_608_, lean_object* v_as_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_607_, v_pivot_608_, v_as_609_, v_i_610_, v_k_611_);
lean_dec(v_pivot_608_);
lean_dec(v_hi_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object* v_n_613_, lean_object* v_as_614_, lean_object* v_lo_615_, lean_object* v_hi_616_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_628_; 
v___x_628_ = lean_nat_dec_lt(v_lo_615_, v_hi_616_);
if (v___x_628_ == 0)
{
lean_dec(v_lo_615_);
return v_as_614_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_mid_631_; lean_object* v___y_633_; lean_object* v___y_639_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_629_ = lean_nat_add(v_lo_615_, v_hi_616_);
v___x_630_ = lean_unsigned_to_nat(1u);
v_mid_631_ = lean_nat_shiftr(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
v___x_644_ = lean_array_fget_borrowed(v_as_614_, v_mid_631_);
v___x_645_ = lean_array_fget_borrowed(v_as_614_, v_lo_615_);
v___x_646_ = l_Lean_Name_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_639_ = v_as_614_;
goto v___jp_638_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_array_fswap(v_as_614_, v_lo_615_, v_mid_631_);
v___y_639_ = v___x_647_;
goto v___jp_638_;
}
v___jp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_array_fget_borrowed(v___y_633_, v_mid_631_);
v___x_635_ = lean_array_fget_borrowed(v___y_633_, v_hi_616_);
v___x_636_ = l_Lean_Name_lt(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_mid_631_);
v___y_618_ = v___y_633_;
goto v___jp_617_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_array_fswap(v___y_633_, v_mid_631_, v_hi_616_);
lean_dec(v_mid_631_);
v___y_618_ = v___x_637_;
goto v___jp_617_;
}
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_array_fget_borrowed(v___y_639_, v_hi_616_);
v___x_641_ = lean_array_fget_borrowed(v___y_639_, v_lo_615_);
v___x_642_ = l_Lean_Name_lt(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
v___y_633_ = v___y_639_;
goto v___jp_632_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_array_fswap(v___y_639_, v_lo_615_, v_hi_616_);
v___y_633_ = v___x_643_;
goto v___jp_632_;
}
}
}
v___jp_617_:
{
lean_object* v_pivot_619_; lean_object* v___x_620_; lean_object* v_fst_621_; lean_object* v_snd_622_; uint8_t v___x_623_; 
v_pivot_619_ = lean_array_fget(v___y_618_, v_hi_616_);
lean_inc_n(v_lo_615_, 2);
v___x_620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_616_, v_pivot_619_, v___y_618_, v_lo_615_, v_lo_615_);
lean_dec(v_pivot_619_);
v_fst_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_fst_621_);
v_snd_622_ = lean_ctor_get(v___x_620_, 1);
lean_inc(v_snd_622_);
lean_dec_ref(v___x_620_);
v___x_623_ = lean_nat_dec_le(v_hi_616_, v_fst_621_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_613_, v_snd_622_, v_lo_615_, v_fst_621_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_fst_621_, v___x_625_);
lean_dec(v_fst_621_);
v_as_614_ = v___x_624_;
v_lo_615_ = v___x_626_;
goto _start;
}
else
{
lean_dec(v_fst_621_);
lean_dec(v_lo_615_);
return v_snd_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object* v_n_648_, lean_object* v_as_649_, lean_object* v_lo_650_, lean_object* v_hi_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_648_, v_as_649_, v_lo_650_, v_hi_651_);
lean_dec(v_hi_651_);
lean_dec(v_n_648_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object* v_scopeParams_657_, lean_object* v_allUserParams_658_, lean_object* v_usedParams_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_659_, v_scopeParams_657_, v_allUserParams_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v_result_662_; lean_object* v___y_664_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___x_680_; lean_object* v___y_682_; lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_661_ = lean_box(0);
lean_inc(v_allUserParams_658_);
v_result_662_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_659_, v___x_661_, v_allUserParams_658_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_array_get_size(v_usedParams_659_);
v___x_689_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__0));
v___x_690_ = lean_nat_dec_lt(v___x_680_, v___x_688_);
if (v___x_690_ == 0)
{
lean_dec(v_allUserParams_658_);
v___y_682_ = v___x_689_;
goto v___jp_681_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_nat_dec_le(v___x_688_, v___x_688_);
if (v___x_691_ == 0)
{
if (v___x_690_ == 0)
{
lean_dec(v_allUserParams_658_);
v___y_682_ = v___x_689_;
goto v___jp_681_;
}
else
{
size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((size_t)0ULL);
v___x_693_ = lean_usize_of_nat(v___x_688_);
v___x_694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_658_, v_usedParams_659_, v___x_692_, v___x_693_, v___x_689_);
lean_dec(v_allUserParams_658_);
v___y_682_ = v___x_694_;
goto v___jp_681_;
}
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_688_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_658_, v_usedParams_659_, v___x_695_, v___x_696_, v___x_689_);
lean_dec(v_allUserParams_658_);
v___y_682_ = v___x_697_;
goto v___jp_681_;
}
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_array_to_list(v___y_664_);
v___x_666_ = l_List_appendTR___redArg(v_result_662_, v___x_665_);
v___x_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
return v___x_667_;
}
v___jp_668_:
{
lean_object* v___x_673_; 
v___x_673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_669_, v___y_671_, v___y_670_, v___y_672_);
lean_dec(v___y_672_);
lean_dec(v___y_669_);
v___y_664_ = v___x_673_;
goto v___jp_663_;
}
v___jp_674_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_le(v___y_678_, v___y_677_);
if (v___x_679_ == 0)
{
lean_dec(v___y_677_);
lean_inc(v___y_678_);
v___y_669_ = v___y_675_;
v___y_670_ = v___y_678_;
v___y_671_ = v___y_676_;
v___y_672_ = v___y_678_;
goto v___jp_668_;
}
else
{
v___y_669_ = v___y_675_;
v___y_670_ = v___y_678_;
v___y_671_ = v___y_676_;
v___y_672_ = v___y_677_;
goto v___jp_668_;
}
}
v___jp_681_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_array_get_size(v___y_682_);
v___x_684_ = lean_nat_dec_eq(v___x_683_, v___x_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v___x_683_, v___x_685_);
v___x_687_ = lean_nat_dec_le(v___x_680_, v___x_686_);
if (v___x_687_ == 0)
{
lean_inc(v___x_686_);
v___y_675_ = v___x_683_;
v___y_676_ = v___y_682_;
v___y_677_ = v___x_686_;
v___y_678_ = v___x_686_;
goto v___jp_674_;
}
else
{
v___y_675_ = v___x_683_;
v___y_676_ = v___y_682_;
v___y_677_ = v___x_686_;
v___y_678_ = v___x_680_;
goto v___jp_674_;
}
}
else
{
v___y_664_ = v___y_682_;
goto v___jp_663_;
}
}
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_allUserParams_658_);
v_val_698_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_711_ == 0)
{
v___x_700_ = v___x_660_;
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_val_698_);
lean_dec(v___x_660_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_711_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_702_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__1));
v___x_703_ = 1;
v___x_704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_698_, v___x_703_);
v___x_705_ = lean_string_append(v___x_702_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__2));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 0, v___x_707_);
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object* v_scopeParams_712_, lean_object* v_allUserParams_713_, lean_object* v_usedParams_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Elab_sortDeclLevelParams(v_scopeParams_712_, v_allUserParams_713_, v_usedParams_714_);
lean_dec_ref(v_usedParams_714_);
lean_dec(v_scopeParams_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object* v_n_716_, lean_object* v_as_717_, lean_object* v_lo_718_, lean_object* v_hi_719_, lean_object* v_w_720_, lean_object* v_hlo_721_, lean_object* v_hhi_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_716_, v_as_717_, v_lo_718_, v_hi_719_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object* v_n_724_, lean_object* v_as_725_, lean_object* v_lo_726_, lean_object* v_hi_727_, lean_object* v_w_728_, lean_object* v_hlo_729_, lean_object* v_hhi_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_724_, v_as_725_, v_lo_726_, v_hi_727_, v_w_728_, v_hlo_729_, v_hhi_730_);
lean_dec(v_hi_727_);
lean_dec(v_n_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object* v_n_732_, lean_object* v_lo_733_, lean_object* v_hi_734_, lean_object* v_hhi_735_, lean_object* v_pivot_736_, lean_object* v_as_737_, lean_object* v_i_738_, lean_object* v_k_739_, lean_object* v_ilo_740_, lean_object* v_ik_741_, lean_object* v_w_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_734_, v_pivot_736_, v_as_737_, v_i_738_, v_k_739_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object* v_n_744_, lean_object* v_lo_745_, lean_object* v_hi_746_, lean_object* v_hhi_747_, lean_object* v_pivot_748_, lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_k_751_, lean_object* v_ilo_752_, lean_object* v_ik_753_, lean_object* v_w_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_744_, v_lo_745_, v_hi_746_, v_hhi_747_, v_pivot_748_, v_as_749_, v_i_750_, v_k_751_, v_ilo_752_, v_ik_753_, v_w_754_);
lean_dec(v_pivot_748_);
lean_dec(v_hi_746_);
lean_dec(v_lo_745_);
lean_dec(v_n_744_);
return v_res_755_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeclUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeclUtil(builtin);
}
#ifdef __cplusplus
}
#endif
