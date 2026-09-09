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
lean_object* l_Lean_mkIdent(lean_object*);
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
lean_object* v___x_90_; lean_object* v_env_91_; lean_object* v___x_92_; lean_object* v_toCold_93_; lean_object* v_mctx_94_; lean_object* v_lctx_95_; lean_object* v_options_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_env_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_env_91_);
lean_dec(v___x_90_);
v___x_92_ = lean_st_ref_get(v___y_86_);
v_toCold_93_ = lean_ctor_get(v___y_87_, 0);
v_mctx_94_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_mctx_94_);
lean_dec(v___x_92_);
v_lctx_95_ = lean_ctor_get(v___y_85_, 2);
v_options_96_ = lean_ctor_get(v_toCold_93_, 2);
lean_inc_ref(v_options_96_);
lean_inc_ref(v_lctx_95_);
v___x_97_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_97_, 0, v_env_91_);
lean_ctor_set(v___x_97_, 1, v_mctx_94_);
lean_ctor_set(v___x_97_, 2, v_lctx_95_);
lean_ctor_set(v___x_97_, 3, v_options_96_);
v___x_98_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v_msgData_84_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_ref_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_ref_113_ = lean_ctor_get(v___y_110_, 2);
v___x_114_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_ref_113_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_ref_113_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0));
v___x_133_ = l_Lean_stringToMessageData(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(lean_object* v_body_134_, lean_object* v_body_135_, lean_object* v_x_136_, lean_object* v_k_137_, lean_object* v_n_138_, lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(v_body_134_, v_body_135_, v_x_136_, v_k_137_, v_n_138_, v_x_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v_n_138_);
lean_dec_ref(v_body_135_);
lean_dec_ref(v_body_134_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3));
v___x_150_ = l_Lean_stringToMessageData(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9));
v___x_159_ = l_Lean_stringToMessageData(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11));
v___x_162_ = l_Lean_stringToMessageData(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15));
v___x_168_ = l_Lean_stringToMessageData(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg(lean_object* v_k_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_zero_179_; uint8_t v_isZero_180_; 
v_zero_179_ = lean_unsigned_to_nat(0u);
v_isZero_180_ = lean_nat_dec_eq(v_x_170_, v_zero_179_);
if (v_isZero_180_ == 1)
{
lean_object* v___x_181_; 
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
v___x_181_ = lean_apply_8(v_k_169_, v_x_173_, v_x_171_, v_x_172_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, lean_box(0));
return v___x_181_;
}
else
{
lean_object* v___x_182_; 
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
v___x_182_ = lean_whnf(v_x_171_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc(v_a_175_);
lean_inc_ref(v_a_174_);
v___x_184_ = lean_whnf(v_x_172_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
if (lean_obj_tag(v_a_183_) == 7)
{
if (lean_obj_tag(v_a_185_) == 7)
{
lean_object* v_binderName_193_; lean_object* v_binderType_194_; lean_object* v_body_195_; uint8_t v_binderInfo_196_; lean_object* v_binderName_197_; lean_object* v_binderType_198_; lean_object* v_body_199_; uint8_t v_binderInfo_200_; lean_object* v_one_201_; lean_object* v_n_202_; lean_object* v___f_203_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_281_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_287_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; uint8_t v___y_291_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; uint8_t v___x_301_; 
v_binderName_193_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_binderName_193_);
v_binderType_194_ = lean_ctor_get(v_a_183_, 1);
lean_inc_ref(v_binderType_194_);
v_body_195_ = lean_ctor_get(v_a_183_, 2);
lean_inc_ref(v_body_195_);
v_binderInfo_196_ = lean_ctor_get_uint8(v_a_183_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_183_, 3);
v_binderName_197_ = lean_ctor_get(v_a_185_, 0);
lean_inc(v_binderName_197_);
v_binderType_198_ = lean_ctor_get(v_a_185_, 1);
lean_inc_ref(v_binderType_198_);
v_body_199_ = lean_ctor_get(v_a_185_, 2);
lean_inc_ref(v_body_199_);
v_binderInfo_200_ = lean_ctor_get_uint8(v_a_185_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_185_, 3);
v_one_201_ = lean_unsigned_to_nat(1u);
v_n_202_ = lean_nat_sub(v_x_170_, v_one_201_);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_203_, 0, v_body_195_);
lean_closure_set(v___f_203_, 1, v_body_199_);
lean_closure_set(v___f_203_, 2, v_x_173_);
lean_closure_set(v___f_203_, 3, v_k_169_);
lean_closure_set(v___f_203_, 4, v_n_202_);
v___x_301_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_196_, v_binderInfo_200_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v___f_203_);
lean_dec_ref(v_binderType_198_);
lean_dec(v_binderName_197_);
lean_dec_ref(v_binderType_194_);
v___x_302_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
v___x_303_ = l_Lean_mkIdent(v_binderName_193_);
v___x_304_ = l_Lean_MessageData_ofSyntax(v___x_303_);
v___x_305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_302_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_307_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
v_a_309_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
v___y_294_ = v_a_174_;
v___y_295_ = v_a_175_;
v___y_296_ = v_a_176_;
v___y_297_ = v_a_177_;
goto v___jp_293_;
}
v___jp_204_:
{
uint8_t v___x_209_; lean_object* v___x_210_; 
v___x_209_ = 0;
v___x_210_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_binderName_193_, v_binderInfo_196_, v_binderType_194_, v___f_203_, v___x_209_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_210_;
}
v___jp_211_:
{
lean_object* v___x_216_; 
lean_inc_ref(v_binderType_198_);
lean_inc_ref(v_binderType_194_);
v___x_216_ = l_Lean_Meta_isExprDefEq(v_binderType_194_, v_binderType_198_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; uint8_t v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = lean_unbox(v_a_217_);
lean_dec(v_a_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
lean_dec_ref(v___f_203_);
v___x_219_ = lean_box(0);
v___x_220_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_221_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_binderType_194_, v_binderType_198_, v___x_219_, v___x_220_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4);
v___x_224_ = l_Lean_mkIdent(v_binderName_193_);
v___x_225_ = l_Lean_MessageData_ofSyntax(v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_a_222_);
v___x_230_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_229_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
v_a_231_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_230_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_230_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_binderName_193_);
v_a_239_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_221_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_221_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_198_);
v___y_205_ = v___y_212_;
v___y_206_ = v___y_213_;
v___y_207_ = v___y_214_;
v___y_208_ = v___y_215_;
goto v___jp_204_;
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v___f_203_);
lean_dec_ref(v_binderType_198_);
lean_dec_ref(v_binderType_194_);
lean_dec(v_binderName_193_);
v_a_247_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_216_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_216_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
v___jp_255_:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v___x_260_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8);
v___x_261_ = l_Lean_mkIdent(v_binderName_193_);
v___x_262_ = l_Lean_MessageData_ofSyntax(v___x_261_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_260_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = l_Lean_mkIdent(v_binderName_197_);
v___x_267_ = l_Lean_MessageData_ofSyntax(v___x_266_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_270_, v___y_256_, v___y_259_, v___y_257_, v___y_258_);
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
v___jp_280_:
{
if (v___y_285_ == 0)
{
lean_dec_ref(v___f_203_);
lean_dec_ref(v_binderType_198_);
lean_dec_ref(v_binderType_194_);
v___y_256_ = v___y_281_;
v___y_257_ = v___y_282_;
v___y_258_ = v___y_283_;
v___y_259_ = v___y_284_;
goto v___jp_255_;
}
else
{
lean_dec(v_binderName_197_);
v___y_212_ = v___y_281_;
v___y_213_ = v___y_284_;
v___y_214_ = v___y_282_;
v___y_215_ = v___y_283_;
goto v___jp_211_;
}
}
v___jp_286_:
{
if (v___y_291_ == 0)
{
lean_dec_ref(v___f_203_);
lean_dec_ref(v_binderType_198_);
lean_dec_ref(v_binderType_194_);
v___y_256_ = v___y_287_;
v___y_257_ = v___y_288_;
v___y_258_ = v___y_289_;
v___y_259_ = v___y_290_;
goto v___jp_255_;
}
else
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_Name_hasMacroScopes(v_binderName_197_);
v___y_281_ = v___y_287_;
v___y_282_ = v___y_288_;
v___y_283_ = v___y_289_;
v___y_284_ = v___y_290_;
v___y_285_ = v___x_292_;
goto v___jp_280_;
}
}
v___jp_293_:
{
uint8_t v___x_298_; 
v___x_298_ = lean_name_eq(v_binderName_193_, v_binderName_197_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_196_);
if (v___x_299_ == 0)
{
v___y_287_ = v___y_294_;
v___y_288_ = v___y_296_;
v___y_289_ = v___y_297_;
v___y_290_ = v___y_295_;
v___y_291_ = v___x_299_;
goto v___jp_286_;
}
else
{
uint8_t v___x_300_; 
v___x_300_ = l_Lean_Name_hasMacroScopes(v_binderName_193_);
v___y_287_ = v___y_294_;
v___y_288_ = v___y_296_;
v___y_289_ = v___y_297_;
v___y_290_ = v___y_295_;
v___y_291_ = v___x_300_;
goto v___jp_286_;
}
}
else
{
v___y_281_ = v___y_294_;
v___y_282_ = v___y_296_;
v___y_283_ = v___y_297_;
v___y_284_ = v___y_295_;
v___y_285_ = v___x_298_;
goto v___jp_280_;
}
}
}
else
{
lean_dec_ref_known(v_a_183_, 3);
lean_dec(v_a_185_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_k_169_);
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_177_;
goto v___jp_186_;
}
}
else
{
lean_dec(v_a_185_);
lean_dec(v_a_183_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_k_169_);
v___y_187_ = v_a_174_;
v___y_188_ = v_a_175_;
v___y_189_ = v_a_176_;
v___y_190_ = v_a_177_;
goto v___jp_186_;
}
v___jp_186_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1);
v___x_192_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_191_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
return v___x_192_;
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec(v_a_183_);
lean_dec_ref(v_x_173_);
lean_dec_ref(v_k_169_);
v_a_317_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_184_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_184_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
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
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v_x_173_);
lean_dec_ref(v_x_172_);
lean_dec_ref(v_k_169_);
v_a_325_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_182_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_182_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object* v_body_333_, lean_object* v_body_334_, lean_object* v_x_335_, lean_object* v_k_336_, lean_object* v_n_337_, lean_object* v_x_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = lean_expr_instantiate1(v_body_333_, v_x_338_);
v___x_345_ = lean_expr_instantiate1(v_body_334_, v_x_338_);
v___x_346_ = lean_array_push(v_x_335_, v_x_338_);
v___x_347_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_336_, v_n_337_, v___x_344_, v___x_345_, v___x_346_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object* v_k_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_348_, v_x_349_, v_x_350_, v_x_351_, v_x_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_x_349_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object* v_00_u03b1_359_, lean_object* v_k_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_360_, v_x_361_, v_x_362_, v_x_363_, v_x_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object* v_00_u03b1_371_, lean_object* v_k_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_forallTelescopeCompatibleAux(v_00_u03b1_371_, v_k_372_, v_x_373_, v_x_374_, v_x_375_, v_x_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_x_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object* v_00_u03b1_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object* v_00_u03b1_391_, lean_object* v_msg_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(v_00_u03b1_391_, v_msg_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object* v_k_399_, lean_object* v_runInBase_400_, lean_object* v_xs_401_, lean_object* v_type_u2081_402_, lean_object* v_type_u2082_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_apply_3(v_k_399_, v_xs_401_, v_type_u2081_402_, v_type_u2082_403_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
lean_inc(v___y_405_);
lean_inc_ref(v___y_404_);
v___x_410_ = lean_apply_7(v_runInBase_400_, lean_box(0), v___x_409_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, lean_box(0));
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object* v_k_411_, lean_object* v_runInBase_412_, lean_object* v_xs_413_, lean_object* v_type_u2081_414_, lean_object* v_type_u2082_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_411_, v_runInBase_412_, v_xs_413_, v_type_u2081_414_, v_type_u2082_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object* v_k_422_, lean_object* v_numParams_423_, lean_object* v_type_u2081_424_, lean_object* v_type_u2082_425_, lean_object* v_runInBase_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___f_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___f_432_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_432_, 0, v_k_422_);
lean_closure_set(v___f_432_, 1, v_runInBase_426_);
v___x_433_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_434_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v___f_432_, v_numParams_423_, v_type_u2081_424_, v_type_u2082_425_, v___x_433_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object* v_k_435_, lean_object* v_numParams_436_, lean_object* v_type_u2081_437_, lean_object* v_type_u2082_438_, lean_object* v_runInBase_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_435_, v_numParams_436_, v_type_u2081_437_, v_type_u2082_438_, v_runInBase_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v_numParams_436_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_type_u2081_448_, lean_object* v_type_u2082_449_, lean_object* v_numParams_450_, lean_object* v_k_451_){
_start:
{
lean_object* v_toBind_452_; lean_object* v_liftWith_453_; lean_object* v_restoreM_454_; lean_object* v___f_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_toBind_452_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_toBind_452_);
lean_dec_ref(v_inst_446_);
v_liftWith_453_ = lean_ctor_get(v_inst_447_, 0);
lean_inc(v_liftWith_453_);
v_restoreM_454_ = lean_ctor_get(v_inst_447_, 1);
lean_inc(v_restoreM_454_);
lean_dec_ref(v_inst_447_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_455_, 0, v_k_451_);
lean_closure_set(v___f_455_, 1, v_numParams_450_);
lean_closure_set(v___f_455_, 2, v_type_u2081_448_);
lean_closure_set(v___f_455_, 3, v_type_u2082_449_);
v___x_456_ = lean_apply_2(v_liftWith_453_, lean_box(0), v___f_455_);
v___x_457_ = lean_apply_1(v_restoreM_454_, lean_box(0));
v___x_458_ = lean_apply_4(v_toBind_452_, lean_box(0), lean_box(0), v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object* v_m_459_, lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_type_u2081_463_, lean_object* v_type_u2082_464_, lean_object* v_numParams_465_, lean_object* v_k_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_forallTelescopeCompatible___redArg(v_inst_461_, v_inst_462_, v_type_u2081_463_, v_type_u2082_464_, v_numParams_465_, v_k_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object* v_stx_468_){
_start:
{
lean_object* v___x_469_; lean_object* v_binders_470_; lean_object* v___x_471_; lean_object* v_optType_472_; uint8_t v___x_473_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v_binders_470_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_469_);
v___x_471_ = lean_unsigned_to_nat(1u);
v_optType_472_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_471_);
v___x_473_ = l_Lean_Syntax_isNone(v_optType_472_);
if (v___x_473_ == 0)
{
lean_object* v_typeSpec_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_typeSpec_474_ = l_Lean_Syntax_getArg(v_optType_472_, v___x_469_);
lean_dec(v_optType_472_);
v___x_475_ = l_Lean_Syntax_getArg(v_typeSpec_474_, v___x_471_);
lean_dec(v_typeSpec_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_binders_470_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_optType_472_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_binders_470_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object* v_stx_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Elab_expandOptDeclSig(v_stx_480_);
lean_dec(v_stx_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object* v_stx_482_){
_start:
{
lean_object* v___x_483_; lean_object* v_binders_484_; lean_object* v___x_485_; lean_object* v_typeSpec_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_483_ = lean_unsigned_to_nat(0u);
v_binders_484_ = l_Lean_Syntax_getArg(v_stx_482_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(1u);
v_typeSpec_486_ = l_Lean_Syntax_getArg(v_stx_482_, v___x_485_);
v___x_487_ = l_Lean_Syntax_getArg(v_typeSpec_486_, v___x_485_);
lean_dec(v_typeSpec_486_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v_binders_484_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object* v_stx_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Elab_expandDeclSig(v_stx_489_);
lean_dec(v_stx_489_);
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object* v_a_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_492_) == 0)
{
uint8_t v___x_493_; 
v___x_493_ = 0;
return v___x_493_;
}
else
{
lean_object* v_head_494_; lean_object* v_tail_495_; uint8_t v___x_496_; 
v_head_494_ = lean_ctor_get(v_x_492_, 0);
v_tail_495_ = lean_ctor_get(v_x_492_, 1);
v___x_496_ = lean_name_eq(v_a_491_, v_head_494_);
if (v___x_496_ == 0)
{
v_x_492_ = v_tail_495_;
goto _start;
}
else
{
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec(v_a_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object* v_allUserParams_502_, lean_object* v_as_503_, size_t v_i_504_, size_t v_stop_505_, lean_object* v_b_506_){
_start:
{
lean_object* v___y_508_; uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_eq(v_i_504_, v_stop_505_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_513_ = lean_array_uget_borrowed(v_as_503_, v_i_504_);
v___x_514_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v___x_513_, v_allUserParams_502_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_inc(v___x_513_);
v___x_515_ = lean_array_push(v_b_506_, v___x_513_);
v___y_508_ = v___x_515_;
goto v___jp_507_;
}
else
{
v___y_508_ = v_b_506_;
goto v___jp_507_;
}
}
else
{
return v_b_506_;
}
v___jp_507_:
{
size_t v___x_509_; size_t v___x_510_; 
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_504_, v___x_509_);
v_i_504_ = v___x_510_;
v_b_506_ = v___y_508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object* v_allUserParams_516_, lean_object* v_as_517_, lean_object* v_i_518_, lean_object* v_stop_519_, lean_object* v_b_520_){
_start:
{
size_t v_i_boxed_521_; size_t v_stop_boxed_522_; lean_object* v_res_523_; 
v_i_boxed_521_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_519_);
lean_dec(v_stop_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_516_, v_as_517_, v_i_boxed_521_, v_stop_boxed_522_, v_b_520_);
lean_dec_ref(v_as_517_);
lean_dec(v_allUserParams_516_);
return v_res_523_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object* v_a_524_, lean_object* v_as_525_, size_t v_i_526_, size_t v_stop_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_eq(v_i_526_, v_stop_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_array_uget_borrowed(v_as_525_, v_i_526_);
v___x_530_ = lean_name_eq(v_a_524_, v___x_529_);
if (v___x_530_ == 0)
{
size_t v___x_531_; size_t v___x_532_; 
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_526_, v___x_531_);
v_i_526_ = v___x_532_;
goto _start;
}
else
{
return v___x_530_;
}
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object* v_a_535_, lean_object* v_as_536_, lean_object* v_i_537_, lean_object* v_stop_538_){
_start:
{
size_t v_i_boxed_539_; size_t v_stop_boxed_540_; uint8_t v_res_541_; lean_object* v_r_542_; 
v_i_boxed_539_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_stop_boxed_540_ = lean_unbox_usize(v_stop_538_);
lean_dec(v_stop_538_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_535_, v_as_536_, v_i_boxed_539_, v_stop_boxed_540_);
lean_dec_ref(v_as_536_);
lean_dec(v_a_535_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object* v_as_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_array_get_size(v_as_543_);
v___x_547_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
return v___x_547_;
}
else
{
if (v___x_547_ == 0)
{
return v___x_547_;
}
else
{
size_t v___x_548_; size_t v___x_549_; uint8_t v___x_550_; 
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_546_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_544_, v_as_543_, v___x_548_, v___x_549_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object* v_as_551_, lean_object* v_a_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_as_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object* v_usedParams_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
return v_x_556_;
}
else
{
lean_object* v_head_558_; lean_object* v_tail_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_569_; 
v_head_558_ = lean_ctor_get(v_x_557_, 0);
v_tail_559_ = lean_ctor_get(v_x_557_, 1);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_557_);
if (v_isSharedCheck_569_ == 0)
{
v___x_561_ = v_x_557_;
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_tail_559_);
lean_inc(v_head_558_);
lean_dec(v_x_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_569_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___x_563_; 
v___x_563_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_555_, v_head_558_);
if (v___x_563_ == 0)
{
lean_del_object(v___x_561_);
lean_dec(v_head_558_);
v_x_557_ = v_tail_559_;
goto _start;
}
else
{
lean_object* v___x_566_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_x_556_);
v___x_566_ = v___x_561_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_head_558_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_x_556_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_x_556_ = v___x_566_;
v_x_557_ = v_tail_559_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object* v_usedParams_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_570_, v_x_571_, v_x_572_);
lean_dec_ref(v_usedParams_570_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object* v_usedParams_574_, lean_object* v_scopeParams_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v_head_578_; lean_object* v_tail_579_; uint8_t v___x_580_; 
v_head_578_ = lean_ctor_get(v_x_576_, 0);
v_tail_579_ = lean_ctor_get(v_x_576_, 1);
v___x_580_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_574_, v_head_578_);
if (v___x_580_ == 0)
{
uint8_t v___x_581_; 
v___x_581_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_head_578_, v_scopeParams_575_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_inc(v_head_578_);
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_head_578_);
return v___x_582_;
}
else
{
if (v___x_580_ == 0)
{
v_x_576_ = v_tail_579_;
goto _start;
}
else
{
lean_object* v___x_584_; 
lean_inc(v_head_578_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_head_578_);
return v___x_584_;
}
}
}
else
{
v_x_576_ = v_tail_579_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object* v_usedParams_586_, lean_object* v_scopeParams_587_, lean_object* v_x_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_586_, v_scopeParams_587_, v_x_588_);
lean_dec(v_x_588_);
lean_dec(v_scopeParams_587_);
lean_dec_ref(v_usedParams_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object* v_hi_590_, lean_object* v_pivot_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_k_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_lt(v_k_594_, v_hi_590_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_k_594_);
v___x_596_ = lean_array_fswap(v_as_592_, v_i_593_, v_hi_590_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_i_593_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_fget_borrowed(v_as_592_, v_k_594_);
v___x_599_ = l_Lean_Name_lt(v___x_598_, v_pivot_591_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_k_594_, v___x_600_);
lean_dec(v_k_594_);
v_k_594_ = v___x_601_;
goto _start;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = lean_array_fswap(v_as_592_, v_i_593_, v_k_594_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_593_, v___x_604_);
lean_dec(v_i_593_);
v___x_606_ = lean_nat_add(v_k_594_, v___x_604_);
lean_dec(v_k_594_);
v_as_592_ = v___x_603_;
v_i_593_ = v___x_605_;
v_k_594_ = v___x_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object* v_hi_608_, lean_object* v_pivot_609_, lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_k_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_608_, v_pivot_609_, v_as_610_, v_i_611_, v_k_612_);
lean_dec(v_pivot_609_);
lean_dec(v_hi_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object* v_n_614_, lean_object* v_as_615_, lean_object* v_lo_616_, lean_object* v_hi_617_){
_start:
{
lean_object* v___y_619_; uint8_t v___x_629_; 
v___x_629_ = lean_nat_dec_lt(v_lo_616_, v_hi_617_);
if (v___x_629_ == 0)
{
lean_dec(v_lo_616_);
return v_as_615_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_mid_632_; lean_object* v___y_634_; lean_object* v___y_640_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_630_ = lean_nat_add(v_lo_616_, v_hi_617_);
v___x_631_ = lean_unsigned_to_nat(1u);
v_mid_632_ = lean_nat_shiftr(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_645_ = lean_array_fget_borrowed(v_as_615_, v_mid_632_);
v___x_646_ = lean_array_fget_borrowed(v_as_615_, v_lo_616_);
v___x_647_ = l_Lean_Name_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
v___y_640_ = v_as_615_;
goto v___jp_639_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_array_fswap(v_as_615_, v_lo_616_, v_mid_632_);
v___y_640_ = v___x_648_;
goto v___jp_639_;
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_array_fget_borrowed(v___y_634_, v_mid_632_);
v___x_636_ = lean_array_fget_borrowed(v___y_634_, v_hi_617_);
v___x_637_ = l_Lean_Name_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_dec(v_mid_632_);
v___y_619_ = v___y_634_;
goto v___jp_618_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_fswap(v___y_634_, v_mid_632_, v_hi_617_);
lean_dec(v_mid_632_);
v___y_619_ = v___x_638_;
goto v___jp_618_;
}
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_array_fget_borrowed(v___y_640_, v_hi_617_);
v___x_642_ = lean_array_fget_borrowed(v___y_640_, v_lo_616_);
v___x_643_ = l_Lean_Name_lt(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
v___y_634_ = v___y_640_;
goto v___jp_633_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_array_fswap(v___y_640_, v_lo_616_, v_hi_617_);
v___y_634_ = v___x_644_;
goto v___jp_633_;
}
}
}
v___jp_618_:
{
lean_object* v_pivot_620_; lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; uint8_t v___x_624_; 
v_pivot_620_ = lean_array_fget(v___y_619_, v_hi_617_);
lean_inc_n(v_lo_616_, 2);
v___x_621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_617_, v_pivot_620_, v___y_619_, v_lo_616_, v_lo_616_);
lean_dec(v_pivot_620_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = lean_nat_dec_le(v_hi_617_, v_fst_622_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_614_, v_snd_623_, v_lo_616_, v_fst_622_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_fst_622_, v___x_626_);
lean_dec(v_fst_622_);
v_as_615_ = v___x_625_;
v_lo_616_ = v___x_627_;
goto _start;
}
else
{
lean_dec(v_fst_622_);
lean_dec(v_lo_616_);
return v_snd_623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object* v_n_649_, lean_object* v_as_650_, lean_object* v_lo_651_, lean_object* v_hi_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_649_, v_as_650_, v_lo_651_, v_hi_652_);
lean_dec(v_hi_652_);
lean_dec(v_n_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object* v_scopeParams_658_, lean_object* v_allUserParams_659_, lean_object* v_usedParams_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_660_, v_scopeParams_658_, v_allUserParams_659_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v___x_662_; lean_object* v_result_663_; lean_object* v___y_665_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___x_681_; lean_object* v___y_683_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_662_ = lean_box(0);
lean_inc(v_allUserParams_659_);
v_result_663_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_660_, v___x_662_, v_allUserParams_659_);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_array_get_size(v_usedParams_660_);
v___x_690_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__0));
v___x_691_ = lean_nat_dec_lt(v___x_681_, v___x_689_);
if (v___x_691_ == 0)
{
lean_dec(v_allUserParams_659_);
v___y_683_ = v___x_690_;
goto v___jp_682_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = lean_nat_dec_le(v___x_689_, v___x_689_);
if (v___x_692_ == 0)
{
if (v___x_691_ == 0)
{
lean_dec(v_allUserParams_659_);
v___y_683_ = v___x_690_;
goto v___jp_682_;
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_689_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_659_, v_usedParams_660_, v___x_693_, v___x_694_, v___x_690_);
lean_dec(v_allUserParams_659_);
v___y_683_ = v___x_695_;
goto v___jp_682_;
}
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_689_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_659_, v_usedParams_660_, v___x_696_, v___x_697_, v___x_690_);
lean_dec(v_allUserParams_659_);
v___y_683_ = v___x_698_;
goto v___jp_682_;
}
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_array_to_list(v___y_665_);
v___x_667_ = l_List_appendTR___redArg(v_result_663_, v___x_666_);
v___x_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_674_; 
v___x_674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_672_, v___y_670_, v___y_671_, v___y_673_);
lean_dec(v___y_673_);
lean_dec(v___y_672_);
v___y_665_ = v___x_674_;
goto v___jp_664_;
}
v___jp_675_:
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___y_679_, v___y_677_);
if (v___x_680_ == 0)
{
lean_dec(v___y_677_);
lean_inc(v___y_679_);
v___y_670_ = v___y_676_;
v___y_671_ = v___y_679_;
v___y_672_ = v___y_678_;
v___y_673_ = v___y_679_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___y_676_;
v___y_671_ = v___y_679_;
v___y_672_ = v___y_678_;
v___y_673_ = v___y_677_;
goto v___jp_669_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_array_get_size(v___y_683_);
v___x_685_ = lean_nat_dec_eq(v___x_684_, v___x_681_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_sub(v___x_684_, v___x_686_);
v___x_688_ = lean_nat_dec_le(v___x_681_, v___x_687_);
if (v___x_688_ == 0)
{
lean_inc(v___x_687_);
v___y_676_ = v___y_683_;
v___y_677_ = v___x_687_;
v___y_678_ = v___x_684_;
v___y_679_ = v___x_687_;
goto v___jp_675_;
}
else
{
v___y_676_ = v___y_683_;
v___y_677_ = v___x_687_;
v___y_678_ = v___x_684_;
v___y_679_ = v___x_681_;
goto v___jp_675_;
}
}
else
{
v___y_665_ = v___y_683_;
goto v___jp_664_;
}
}
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_allUserParams_659_);
v_val_699_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_712_ == 0)
{
v___x_701_ = v___x_661_;
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_661_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_712_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_703_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__1));
v___x_704_ = 1;
v___x_705_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_699_, v___x_704_);
v___x_706_ = lean_string_append(v___x_703_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__2));
v___x_708_ = lean_string_append(v___x_706_, v___x_707_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 0, v___x_708_);
v___x_710_ = v___x_701_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object* v_scopeParams_713_, lean_object* v_allUserParams_714_, lean_object* v_usedParams_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Elab_sortDeclLevelParams(v_scopeParams_713_, v_allUserParams_714_, v_usedParams_715_);
lean_dec_ref(v_usedParams_715_);
lean_dec(v_scopeParams_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object* v_n_717_, lean_object* v_as_718_, lean_object* v_lo_719_, lean_object* v_hi_720_, lean_object* v_w_721_, lean_object* v_hlo_722_, lean_object* v_hhi_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_717_, v_as_718_, v_lo_719_, v_hi_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object* v_n_725_, lean_object* v_as_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_w_729_, lean_object* v_hlo_730_, lean_object* v_hhi_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_725_, v_as_726_, v_lo_727_, v_hi_728_, v_w_729_, v_hlo_730_, v_hhi_731_);
lean_dec(v_hi_728_);
lean_dec(v_n_725_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object* v_n_733_, lean_object* v_lo_734_, lean_object* v_hi_735_, lean_object* v_hhi_736_, lean_object* v_pivot_737_, lean_object* v_as_738_, lean_object* v_i_739_, lean_object* v_k_740_, lean_object* v_ilo_741_, lean_object* v_ik_742_, lean_object* v_w_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_735_, v_pivot_737_, v_as_738_, v_i_739_, v_k_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object* v_n_745_, lean_object* v_lo_746_, lean_object* v_hi_747_, lean_object* v_hhi_748_, lean_object* v_pivot_749_, lean_object* v_as_750_, lean_object* v_i_751_, lean_object* v_k_752_, lean_object* v_ilo_753_, lean_object* v_ik_754_, lean_object* v_w_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_745_, v_lo_746_, v_hi_747_, v_hhi_748_, v_pivot_749_, v_as_750_, v_i_751_, v_k_752_, v_ilo_753_, v_ik_754_, v_w_755_);
lean_dec(v_pivot_749_);
lean_dec(v_hi_747_);
lean_dec(v_lo_746_);
lean_dec(v_n_745_);
return v_res_756_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeclUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
