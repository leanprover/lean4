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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_90_; lean_object* v_env_91_; uint8_t v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_toCold_95_; lean_object* v_mctx_96_; lean_object* v_lctx_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_env_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_env_91_);
lean_dec(v___x_90_);
v___x_92_ = 0;
v_env_93_ = l_Lean_Environment_setRecordingDeps(v_env_91_, v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_86_);
v_toCold_95_ = lean_ctor_get(v___y_87_, 0);
v_mctx_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_94_);
v_lctx_97_ = lean_ctor_get(v___y_85_, 2);
v_options_98_ = lean_ctor_get(v_toCold_95_, 2);
lean_inc_ref(v_options_98_);
lean_inc_ref(v_lctx_97_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_env_93_);
lean_ctor_set(v___x_99_, 1, v_mctx_96_);
lean_ctor_set(v___x_99_, 2, v_lctx_97_);
lean_ctor_set(v___x_99_, 3, v_options_98_);
v___x_100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_msgData_84_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_125_; 
v_ref_115_ = lean_ctor_get(v___y_112_, 2);
v___x_116_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_125_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_125_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_121_; lean_object* v___x_123_; 
lean_inc(v_ref_115_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_115_);
lean_ctor_set(v___x_121_, 1, v_a_117_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 1);
lean_ctor_set(v___x_119_, 0, v___x_121_);
v___x_123_ = v___x_119_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(lean_object* v_msg_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0));
v___x_135_ = l_Lean_stringToMessageData(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(lean_object* v_body_136_, lean_object* v_body_137_, lean_object* v_x_138_, lean_object* v_k_139_, lean_object* v_n_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(v_body_136_, v_body_137_, v_x_138_, v_k_139_, v_n_140_, v_x_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v_n_140_);
lean_dec_ref(v_body_137_);
lean_dec_ref(v_body_136_);
return v_res_147_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3));
v___x_152_ = l_Lean_stringToMessageData(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg(lean_object* v_k_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v_zero_188_; uint8_t v_isZero_189_; 
v_zero_188_ = lean_unsigned_to_nat(0u);
v_isZero_189_ = lean_nat_dec_eq(v_x_172_, v_zero_188_);
if (v_isZero_189_ == 1)
{
lean_object* v___x_190_; 
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
v___x_190_ = lean_apply_8(v_k_171_, v_x_175_, v_x_173_, v_x_174_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, lean_box(0));
return v___x_190_;
}
else
{
lean_object* v_one_191_; lean_object* v_n_192_; lean_object* v___x_193_; 
v_one_191_ = lean_unsigned_to_nat(1u);
v_n_192_ = lean_nat_sub(v_x_172_, v_one_191_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
v___x_193_ = lean_whnf(v_x_173_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_193_, 1);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
v___x_195_ = lean_whnf(v_x_174_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_195_) == 0)
{
if (lean_obj_tag(v_a_194_) == 7)
{
lean_object* v_a_196_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_195_, 1);
if (lean_obj_tag(v_a_196_) == 7)
{
lean_object* v_binderName_197_; lean_object* v_binderType_198_; lean_object* v_body_199_; uint8_t v_binderInfo_200_; lean_object* v_binderName_201_; lean_object* v_binderType_202_; lean_object* v_body_203_; uint8_t v_binderInfo_204_; lean_object* v___f_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_293_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___x_303_; 
v_binderName_197_ = lean_ctor_get(v_a_194_, 0);
lean_inc(v_binderName_197_);
v_binderType_198_ = lean_ctor_get(v_a_194_, 1);
lean_inc_ref(v_binderType_198_);
v_body_199_ = lean_ctor_get(v_a_194_, 2);
lean_inc_ref(v_body_199_);
v_binderInfo_200_ = lean_ctor_get_uint8(v_a_194_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_194_, 3);
v_binderName_201_ = lean_ctor_get(v_a_196_, 0);
lean_inc(v_binderName_201_);
v_binderType_202_ = lean_ctor_get(v_a_196_, 1);
lean_inc_ref(v_binderType_202_);
v_body_203_ = lean_ctor_get(v_a_196_, 2);
lean_inc_ref(v_body_203_);
v_binderInfo_204_ = lean_ctor_get_uint8(v_a_196_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_196_, 3);
v___f_205_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_205_, 0, v_body_199_);
lean_closure_set(v___f_205_, 1, v_body_203_);
lean_closure_set(v___f_205_, 2, v_x_175_);
lean_closure_set(v___f_205_, 3, v_k_171_);
lean_closure_set(v___f_205_, 4, v_n_192_);
v___x_303_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_200_, v_binderInfo_204_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec(v_binderName_201_);
lean_dec_ref(v_binderType_198_);
v___x_304_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
v___x_305_ = l_Lean_mkIdent(v_binderName_197_);
v___x_306_ = l_Lean_MessageData_ofSyntax(v___x_305_);
v___x_307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_304_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
v___x_309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_309_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
v___y_296_ = v_a_176_;
v___y_297_ = v_a_177_;
v___y_298_ = v_a_178_;
v___y_299_ = v_a_179_;
goto v___jp_295_;
}
v___jp_206_:
{
uint8_t v___x_211_; lean_object* v___x_212_; 
v___x_211_ = 0;
v___x_212_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_binderName_197_, v_binderInfo_200_, v_binderType_198_, v___f_205_, v___x_211_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
return v___x_212_;
}
v___jp_213_:
{
lean_object* v___x_218_; 
lean_inc_ref(v_binderType_202_);
lean_inc_ref(v_binderType_198_);
v___x_218_ = l_Lean_Meta_isExprDefEq(v_binderType_198_, v_binderType_202_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; uint8_t v___x_220_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
lean_dec_ref_known(v___x_218_, 1);
v___x_220_ = lean_unbox(v_a_219_);
lean_dec(v_a_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v___f_205_);
v___x_221_ = lean_box(0);
v___x_222_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_223_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_binderType_198_, v_binderType_202_, v___x_221_, v___x_222_, v___y_214_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4);
v___x_226_ = l_Lean_mkIdent(v_binderName_197_);
v___x_227_ = l_Lean_MessageData_ofSyntax(v___x_226_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_225_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_a_224_);
v___x_232_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_231_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_binderName_197_);
v_a_241_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_223_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_223_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_202_);
v___y_207_ = v___y_214_;
v___y_208_ = v___y_215_;
v___y_209_ = v___y_216_;
v___y_210_ = v___y_217_;
goto v___jp_206_;
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
lean_dec(v_binderName_197_);
v_a_249_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_218_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_218_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
v___jp_257_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v___x_262_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8);
v___x_263_ = l_Lean_mkIdent(v_binderName_197_);
v___x_264_ = l_Lean_MessageData_ofSyntax(v___x_263_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_mkIdent(v_binderName_201_);
v___x_269_ = l_Lean_MessageData_ofSyntax(v___x_268_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_272_, v___y_259_, v___y_258_, v___y_261_, v___y_260_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
v___jp_282_:
{
if (v___y_287_ == 0)
{
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
v___y_258_ = v___y_283_;
v___y_259_ = v___y_284_;
v___y_260_ = v___y_285_;
v___y_261_ = v___y_286_;
goto v___jp_257_;
}
else
{
lean_dec(v_binderName_201_);
v___y_214_ = v___y_284_;
v___y_215_ = v___y_283_;
v___y_216_ = v___y_286_;
v___y_217_ = v___y_285_;
goto v___jp_213_;
}
}
v___jp_288_:
{
if (v___y_293_ == 0)
{
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
v___y_258_ = v___y_289_;
v___y_259_ = v___y_290_;
v___y_260_ = v___y_291_;
v___y_261_ = v___y_292_;
goto v___jp_257_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = l_Lean_Name_hasMacroScopes(v_binderName_201_);
v___y_283_ = v___y_289_;
v___y_284_ = v___y_290_;
v___y_285_ = v___y_291_;
v___y_286_ = v___y_292_;
v___y_287_ = v___x_294_;
goto v___jp_282_;
}
}
v___jp_295_:
{
uint8_t v___x_300_; 
v___x_300_ = lean_name_eq(v_binderName_197_, v_binderName_201_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_200_);
if (v___x_301_ == 0)
{
v___y_289_ = v___y_297_;
v___y_290_ = v___y_296_;
v___y_291_ = v___y_299_;
v___y_292_ = v___y_298_;
v___y_293_ = v___x_301_;
goto v___jp_288_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = l_Lean_Name_hasMacroScopes(v_binderName_197_);
v___y_289_ = v___y_297_;
v___y_290_ = v___y_296_;
v___y_291_ = v___y_299_;
v___y_292_ = v___y_298_;
v___y_293_ = v___x_302_;
goto v___jp_288_;
}
}
else
{
v___y_283_ = v___y_297_;
v___y_284_ = v___y_296_;
v___y_285_ = v___y_299_;
v___y_286_ = v___y_298_;
v___y_287_ = v___x_300_;
goto v___jp_282_;
}
}
}
else
{
lean_dec(v_a_196_);
lean_dec_ref_known(v_a_194_, 3);
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_k_171_);
v___y_182_ = v_a_176_;
v___y_183_ = v_a_177_;
v___y_184_ = v_a_178_;
v___y_185_ = v_a_179_;
goto v___jp_181_;
}
}
else
{
lean_dec_ref_known(v___x_195_, 1);
lean_dec(v_a_194_);
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_k_171_);
v___y_182_ = v_a_176_;
v___y_183_ = v_a_177_;
v___y_184_ = v_a_178_;
v___y_185_ = v_a_179_;
goto v___jp_181_;
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
lean_dec(v_a_194_);
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_k_171_);
v_a_319_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_195_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_195_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_x_174_);
lean_dec_ref(v_k_171_);
v_a_327_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_193_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_193_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
v___jp_181_:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1);
v___x_187_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_186_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object* v_body_335_, lean_object* v_body_336_, lean_object* v_x_337_, lean_object* v_k_338_, lean_object* v_n_339_, lean_object* v_x_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_expr_instantiate1(v_body_335_, v_x_340_);
v___x_347_ = lean_expr_instantiate1(v_body_336_, v_x_340_);
v___x_348_ = lean_array_push(v_x_337_, v_x_340_);
v___x_349_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_338_, v_n_339_, v___x_346_, v___x_347_, v___x_348_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object* v_k_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_350_, v_x_351_, v_x_352_, v_x_353_, v_x_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_x_351_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object* v_00_u03b1_361_, lean_object* v_k_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_362_, v_x_363_, v_x_364_, v_x_365_, v_x_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object* v_00_u03b1_373_, lean_object* v_k_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_forallTelescopeCompatibleAux(v_00_u03b1_373_, v_k_374_, v_x_375_, v_x_376_, v_x_377_, v_x_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_x_375_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object* v_00_u03b1_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(v_00_u03b1_393_, v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object* v_k_401_, lean_object* v_runInBase_402_, lean_object* v_xs_403_, lean_object* v_type_u2081_404_, lean_object* v_type_u2082_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_apply_3(v_k_401_, v_xs_403_, v_type_u2081_404_, v_type_u2082_405_);
lean_inc(v___y_409_);
lean_inc_ref(v___y_408_);
lean_inc(v___y_407_);
lean_inc_ref(v___y_406_);
v___x_412_ = lean_apply_7(v_runInBase_402_, lean_box(0), v___x_411_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, lean_box(0));
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object* v_k_413_, lean_object* v_runInBase_414_, lean_object* v_xs_415_, lean_object* v_type_u2081_416_, lean_object* v_type_u2082_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_413_, v_runInBase_414_, v_xs_415_, v_type_u2081_416_, v_type_u2082_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object* v_k_424_, lean_object* v_numParams_425_, lean_object* v_type_u2081_426_, lean_object* v_type_u2082_427_, lean_object* v_runInBase_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_434_, 0, v_k_424_);
lean_closure_set(v___f_434_, 1, v_runInBase_428_);
v___x_435_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_436_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v___f_434_, v_numParams_425_, v_type_u2081_426_, v_type_u2082_427_, v___x_435_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object* v_k_437_, lean_object* v_numParams_438_, lean_object* v_type_u2081_439_, lean_object* v_type_u2082_440_, lean_object* v_runInBase_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_437_, v_numParams_438_, v_type_u2081_439_, v_type_u2082_440_, v_runInBase_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v_numParams_438_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_type_u2081_450_, lean_object* v_type_u2082_451_, lean_object* v_numParams_452_, lean_object* v_k_453_){
_start:
{
lean_object* v_toBind_454_; lean_object* v_liftWith_455_; lean_object* v_restoreM_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_toBind_454_ = lean_ctor_get(v_inst_448_, 1);
lean_inc(v_toBind_454_);
lean_dec_ref(v_inst_448_);
v_liftWith_455_ = lean_ctor_get(v_inst_449_, 0);
lean_inc(v_liftWith_455_);
v_restoreM_456_ = lean_ctor_get(v_inst_449_, 1);
lean_inc(v_restoreM_456_);
lean_dec_ref(v_inst_449_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_457_, 0, v_k_453_);
lean_closure_set(v___f_457_, 1, v_numParams_452_);
lean_closure_set(v___f_457_, 2, v_type_u2081_450_);
lean_closure_set(v___f_457_, 3, v_type_u2082_451_);
v___x_458_ = lean_apply_2(v_liftWith_455_, lean_box(0), v___f_457_);
v___x_459_ = lean_apply_1(v_restoreM_456_, lean_box(0));
v___x_460_ = lean_apply_4(v_toBind_454_, lean_box(0), lean_box(0), v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object* v_m_461_, lean_object* v_00_u03b1_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_type_u2081_465_, lean_object* v_type_u2082_466_, lean_object* v_numParams_467_, lean_object* v_k_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_forallTelescopeCompatible___redArg(v_inst_463_, v_inst_464_, v_type_u2081_465_, v_type_u2082_466_, v_numParams_467_, v_k_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object* v_stx_470_){
_start:
{
lean_object* v___x_471_; lean_object* v_binders_472_; lean_object* v___x_473_; lean_object* v_optType_474_; uint8_t v___x_475_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v_binders_472_ = l_Lean_Syntax_getArg(v_stx_470_, v___x_471_);
v___x_473_ = lean_unsigned_to_nat(1u);
v_optType_474_ = l_Lean_Syntax_getArg(v_stx_470_, v___x_473_);
v___x_475_ = l_Lean_Syntax_isNone(v_optType_474_);
if (v___x_475_ == 0)
{
lean_object* v_typeSpec_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_typeSpec_476_ = l_Lean_Syntax_getArg(v_optType_474_, v___x_471_);
lean_dec(v_optType_474_);
v___x_477_ = l_Lean_Syntax_getArg(v_typeSpec_476_, v___x_473_);
lean_dec(v_typeSpec_476_);
v___x_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_binders_472_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_dec(v_optType_474_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_binders_472_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object* v_stx_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Elab_expandOptDeclSig(v_stx_482_);
lean_dec(v_stx_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object* v_stx_484_){
_start:
{
lean_object* v___x_485_; lean_object* v_binders_486_; lean_object* v___x_487_; lean_object* v_typeSpec_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v_binders_486_ = l_Lean_Syntax_getArg(v_stx_484_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(1u);
v_typeSpec_488_ = l_Lean_Syntax_getArg(v_stx_484_, v___x_487_);
v___x_489_ = l_Lean_Syntax_getArg(v_typeSpec_488_, v___x_487_);
lean_dec(v_typeSpec_488_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_binders_486_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object* v_stx_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Elab_expandDeclSig(v_stx_491_);
lean_dec(v_stx_491_);
return v_res_492_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object* v_a_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
uint8_t v___x_495_; 
v___x_495_ = 0;
return v___x_495_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; uint8_t v___x_498_; 
v_head_496_ = lean_ctor_get(v_x_494_, 0);
v_tail_497_ = lean_ctor_get(v_x_494_, 1);
v___x_498_ = lean_name_eq(v_a_493_, v_head_496_);
if (v___x_498_ == 0)
{
v_x_494_ = v_tail_497_;
goto _start;
}
else
{
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object* v_a_500_, lean_object* v_x_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec(v_a_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object* v_allUserParams_504_, lean_object* v_as_505_, size_t v_i_506_, size_t v_stop_507_, lean_object* v_b_508_){
_start:
{
lean_object* v___y_510_; uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_506_, v_stop_507_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_uget_borrowed(v_as_505_, v_i_506_);
v___x_516_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v___x_515_, v_allUserParams_504_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_inc(v___x_515_);
v___x_517_ = lean_array_push(v_b_508_, v___x_515_);
v___y_510_ = v___x_517_;
goto v___jp_509_;
}
else
{
v___y_510_ = v_b_508_;
goto v___jp_509_;
}
}
else
{
return v_b_508_;
}
v___jp_509_:
{
size_t v___x_511_; size_t v___x_512_; 
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_506_, v___x_511_);
v_i_506_ = v___x_512_;
v_b_508_ = v___y_510_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object* v_allUserParams_518_, lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_, lean_object* v_b_522_){
_start:
{
size_t v_i_boxed_523_; size_t v_stop_boxed_524_; lean_object* v_res_525_; 
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_524_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_518_, v_as_519_, v_i_boxed_523_, v_stop_boxed_524_, v_b_522_);
lean_dec_ref(v_as_519_);
lean_dec(v_allUserParams_518_);
return v_res_525_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object* v_a_526_, lean_object* v_as_527_, size_t v_i_528_, size_t v_stop_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = lean_usize_dec_eq(v_i_528_, v_stop_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_531_ = lean_array_uget_borrowed(v_as_527_, v_i_528_);
v___x_532_ = lean_name_eq(v_a_526_, v___x_531_);
if (v___x_532_ == 0)
{
size_t v___x_533_; size_t v___x_534_; 
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_528_, v___x_533_);
v_i_528_ = v___x_534_;
goto _start;
}
else
{
return v___x_532_;
}
}
else
{
uint8_t v___x_536_; 
v___x_536_ = 0;
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object* v_a_537_, lean_object* v_as_538_, lean_object* v_i_539_, lean_object* v_stop_540_){
_start:
{
size_t v_i_boxed_541_; size_t v_stop_boxed_542_; uint8_t v_res_543_; lean_object* v_r_544_; 
v_i_boxed_541_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_stop_boxed_542_ = lean_unbox_usize(v_stop_540_);
lean_dec(v_stop_540_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_537_, v_as_538_, v_i_boxed_541_, v_stop_boxed_542_);
lean_dec_ref(v_as_538_);
lean_dec(v_a_537_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object* v_as_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_array_get_size(v_as_545_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
size_t v___x_550_; size_t v___x_551_; uint8_t v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_548_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_546_, v_as_545_, v___x_550_, v___x_551_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object* v_as_553_, lean_object* v_a_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_as_553_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object* v_usedParams_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
return v_x_558_;
}
else
{
lean_object* v_head_560_; lean_object* v_tail_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_571_; 
v_head_560_ = lean_ctor_get(v_x_559_, 0);
v_tail_561_ = lean_ctor_get(v_x_559_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_571_ == 0)
{
v___x_563_ = v_x_559_;
v_isShared_564_ = v_isSharedCheck_571_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_tail_561_);
lean_inc(v_head_560_);
lean_dec(v_x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_571_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint8_t v___x_565_; 
v___x_565_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_557_, v_head_560_);
if (v___x_565_ == 0)
{
lean_del_object(v___x_563_);
lean_dec(v_head_560_);
v_x_559_ = v_tail_561_;
goto _start;
}
else
{
lean_object* v___x_568_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_x_558_);
v___x_568_ = v___x_563_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_head_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_x_558_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v_x_558_ = v___x_568_;
v_x_559_ = v_tail_561_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object* v_usedParams_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_572_, v_x_573_, v_x_574_);
lean_dec_ref(v_usedParams_572_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object* v_usedParams_576_, lean_object* v_scopeParams_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_head_580_; lean_object* v_tail_581_; uint8_t v___x_582_; 
v_head_580_ = lean_ctor_get(v_x_578_, 0);
v_tail_581_ = lean_ctor_get(v_x_578_, 1);
v___x_582_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_576_, v_head_580_);
if (v___x_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_head_580_, v_scopeParams_577_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_inc(v_head_580_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_head_580_);
return v___x_584_;
}
else
{
if (v___x_582_ == 0)
{
v_x_578_ = v_tail_581_;
goto _start;
}
else
{
lean_object* v___x_586_; 
lean_inc(v_head_580_);
v___x_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_586_, 0, v_head_580_);
return v___x_586_;
}
}
}
else
{
v_x_578_ = v_tail_581_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object* v_usedParams_588_, lean_object* v_scopeParams_589_, lean_object* v_x_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_588_, v_scopeParams_589_, v_x_590_);
lean_dec(v_x_590_);
lean_dec(v_scopeParams_589_);
lean_dec_ref(v_usedParams_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object* v_hi_592_, lean_object* v_pivot_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_k_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_lt(v_k_596_, v_hi_592_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_k_596_);
v___x_598_ = lean_array_fswap(v_as_594_, v_i_595_, v_hi_592_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_i_595_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_fget_borrowed(v_as_594_, v_k_596_);
v___x_601_ = l_Lean_Name_lt(v___x_600_, v_pivot_593_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_k_596_, v___x_602_);
lean_dec(v_k_596_);
v_k_596_ = v___x_603_;
goto _start;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_array_fswap(v_as_594_, v_i_595_, v_k_596_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_i_595_, v___x_606_);
lean_dec(v_i_595_);
v___x_608_ = lean_nat_add(v_k_596_, v___x_606_);
lean_dec(v_k_596_);
v_as_594_ = v___x_605_;
v_i_595_ = v___x_607_;
v_k_596_ = v___x_608_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object* v_hi_610_, lean_object* v_pivot_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_k_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_610_, v_pivot_611_, v_as_612_, v_i_613_, v_k_614_);
lean_dec(v_pivot_611_);
lean_dec(v_hi_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object* v_n_616_, lean_object* v_as_617_, lean_object* v_lo_618_, lean_object* v_hi_619_){
_start:
{
lean_object* v___y_621_; uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_lt(v_lo_618_, v_hi_619_);
if (v___x_631_ == 0)
{
lean_dec(v_lo_618_);
return v_as_617_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_mid_634_; lean_object* v___y_636_; lean_object* v___y_642_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_632_ = lean_nat_add(v_lo_618_, v_hi_619_);
v___x_633_ = lean_unsigned_to_nat(1u);
v_mid_634_ = lean_nat_shiftr(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
v___x_647_ = lean_array_fget_borrowed(v_as_617_, v_mid_634_);
v___x_648_ = lean_array_fget_borrowed(v_as_617_, v_lo_618_);
v___x_649_ = l_Lean_Name_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
v___y_642_ = v_as_617_;
goto v___jp_641_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_array_fswap(v_as_617_, v_lo_618_, v_mid_634_);
v___y_642_ = v___x_650_;
goto v___jp_641_;
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_array_fget_borrowed(v___y_636_, v_mid_634_);
v___x_638_ = lean_array_fget_borrowed(v___y_636_, v_hi_619_);
v___x_639_ = l_Lean_Name_lt(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_dec(v_mid_634_);
v___y_621_ = v___y_636_;
goto v___jp_620_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_array_fswap(v___y_636_, v_mid_634_, v_hi_619_);
lean_dec(v_mid_634_);
v___y_621_ = v___x_640_;
goto v___jp_620_;
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_array_fget_borrowed(v___y_642_, v_hi_619_);
v___x_644_ = lean_array_fget_borrowed(v___y_642_, v_lo_618_);
v___x_645_ = l_Lean_Name_lt(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_636_ = v___y_642_;
goto v___jp_635_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_fswap(v___y_642_, v_lo_618_, v_hi_619_);
v___y_636_ = v___x_646_;
goto v___jp_635_;
}
}
}
v___jp_620_:
{
lean_object* v_pivot_622_; lean_object* v___x_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; uint8_t v___x_626_; 
v_pivot_622_ = lean_array_fget(v___y_621_, v_hi_619_);
lean_inc_n(v_lo_618_, 2);
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_619_, v_pivot_622_, v___y_621_, v_lo_618_, v_lo_618_);
lean_dec(v_pivot_622_);
v_fst_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_fst_624_);
v_snd_625_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_snd_625_);
lean_dec_ref(v___x_623_);
v___x_626_ = lean_nat_dec_le(v_hi_619_, v_fst_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_616_, v_snd_625_, v_lo_618_, v_fst_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_fst_624_, v___x_628_);
lean_dec(v_fst_624_);
v_as_617_ = v___x_627_;
v_lo_618_ = v___x_629_;
goto _start;
}
else
{
lean_dec(v_fst_624_);
lean_dec(v_lo_618_);
return v_snd_625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object* v_n_651_, lean_object* v_as_652_, lean_object* v_lo_653_, lean_object* v_hi_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_651_, v_as_652_, v_lo_653_, v_hi_654_);
lean_dec(v_hi_654_);
lean_dec(v_n_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object* v_scopeParams_660_, lean_object* v_allUserParams_661_, lean_object* v_usedParams_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_662_, v_scopeParams_660_, v_allUserParams_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_664_; lean_object* v_result_665_; lean_object* v___y_667_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___x_683_; lean_object* v___y_685_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_664_ = lean_box(0);
lean_inc(v_allUserParams_661_);
v_result_665_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_662_, v___x_664_, v_allUserParams_661_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_usedParams_662_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__0));
v___x_693_ = lean_nat_dec_lt(v___x_683_, v___x_691_);
if (v___x_693_ == 0)
{
lean_dec(v_allUserParams_661_);
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
uint8_t v___x_694_; 
v___x_694_ = lean_nat_dec_le(v___x_691_, v___x_691_);
if (v___x_694_ == 0)
{
if (v___x_693_ == 0)
{
lean_dec(v_allUserParams_661_);
v___y_685_ = v___x_692_;
goto v___jp_684_;
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_691_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_661_, v_usedParams_662_, v___x_695_, v___x_696_, v___x_692_);
lean_dec(v_allUserParams_661_);
v___y_685_ = v___x_697_;
goto v___jp_684_;
}
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_691_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_661_, v_usedParams_662_, v___x_698_, v___x_699_, v___x_692_);
lean_dec(v_allUserParams_661_);
v___y_685_ = v___x_700_;
goto v___jp_684_;
}
}
v___jp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_array_to_list(v___y_667_);
v___x_669_ = l_List_appendTR___redArg(v_result_665_, v___x_668_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
v___jp_671_:
{
lean_object* v___x_676_; 
v___x_676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_672_, v___y_674_, v___y_673_, v___y_675_);
lean_dec(v___y_675_);
lean_dec(v___y_672_);
v___y_667_ = v___x_676_;
goto v___jp_666_;
}
v___jp_677_:
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_le(v___y_681_, v___y_678_);
if (v___x_682_ == 0)
{
lean_dec(v___y_678_);
lean_inc(v___y_681_);
v___y_672_ = v___y_679_;
v___y_673_ = v___y_681_;
v___y_674_ = v___y_680_;
v___y_675_ = v___y_681_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___y_679_;
v___y_673_ = v___y_681_;
v___y_674_ = v___y_680_;
v___y_675_ = v___y_678_;
goto v___jp_671_;
}
}
v___jp_684_:
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = lean_array_get_size(v___y_685_);
v___x_687_ = lean_nat_dec_eq(v___x_686_, v___x_683_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(1u);
v___x_689_ = lean_nat_sub(v___x_686_, v___x_688_);
v___x_690_ = lean_nat_dec_le(v___x_683_, v___x_689_);
if (v___x_690_ == 0)
{
lean_inc(v___x_689_);
v___y_678_ = v___x_689_;
v___y_679_ = v___x_686_;
v___y_680_ = v___y_685_;
v___y_681_ = v___x_689_;
goto v___jp_677_;
}
else
{
v___y_678_ = v___x_689_;
v___y_679_ = v___x_686_;
v___y_680_ = v___y_685_;
v___y_681_ = v___x_683_;
goto v___jp_677_;
}
}
else
{
v___y_667_ = v___y_685_;
goto v___jp_666_;
}
}
}
else
{
lean_object* v_val_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_allUserParams_661_);
v_val_701_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_714_ == 0)
{
v___x_703_ = v___x_663_;
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_val_701_);
lean_dec(v___x_663_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_714_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_705_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__1));
v___x_706_ = 1;
v___x_707_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_701_, v___x_706_);
v___x_708_ = lean_string_append(v___x_705_, v___x_707_);
lean_dec_ref(v___x_707_);
v___x_709_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__2));
v___x_710_ = lean_string_append(v___x_708_, v___x_709_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 0);
lean_ctor_set(v___x_703_, 0, v___x_710_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object* v_scopeParams_715_, lean_object* v_allUserParams_716_, lean_object* v_usedParams_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_Elab_sortDeclLevelParams(v_scopeParams_715_, v_allUserParams_716_, v_usedParams_717_);
lean_dec_ref(v_usedParams_717_);
lean_dec(v_scopeParams_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object* v_n_719_, lean_object* v_as_720_, lean_object* v_lo_721_, lean_object* v_hi_722_, lean_object* v_w_723_, lean_object* v_hlo_724_, lean_object* v_hhi_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_719_, v_as_720_, v_lo_721_, v_hi_722_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object* v_n_727_, lean_object* v_as_728_, lean_object* v_lo_729_, lean_object* v_hi_730_, lean_object* v_w_731_, lean_object* v_hlo_732_, lean_object* v_hhi_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_727_, v_as_728_, v_lo_729_, v_hi_730_, v_w_731_, v_hlo_732_, v_hhi_733_);
lean_dec(v_hi_730_);
lean_dec(v_n_727_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object* v_n_735_, lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_hhi_738_, lean_object* v_pivot_739_, lean_object* v_as_740_, lean_object* v_i_741_, lean_object* v_k_742_, lean_object* v_ilo_743_, lean_object* v_ik_744_, lean_object* v_w_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_737_, v_pivot_739_, v_as_740_, v_i_741_, v_k_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object* v_n_747_, lean_object* v_lo_748_, lean_object* v_hi_749_, lean_object* v_hhi_750_, lean_object* v_pivot_751_, lean_object* v_as_752_, lean_object* v_i_753_, lean_object* v_k_754_, lean_object* v_ilo_755_, lean_object* v_ik_756_, lean_object* v_w_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_747_, v_lo_748_, v_hi_749_, v_hhi_750_, v_pivot_751_, v_as_752_, v_i_753_, v_k_754_, v_ilo_755_, v_ik_756_, v_w_757_);
lean_dec(v_pivot_751_);
lean_dec(v_hi_749_);
lean_dec(v_lo_748_);
lean_dec(v_n_747_);
return v_res_758_;
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
