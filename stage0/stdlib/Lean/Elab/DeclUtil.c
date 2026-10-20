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
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
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
lean_object* v_binderName_197_; lean_object* v_binderType_198_; lean_object* v_body_199_; uint8_t v_binderInfo_200_; lean_object* v_binderName_201_; lean_object* v_binderType_202_; lean_object* v_body_203_; uint8_t v_binderInfo_204_; lean_object* v___f_205_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___x_291_; 
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
v___x_291_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_200_, v_binderInfo_204_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec(v_binderName_201_);
lean_dec_ref(v_binderType_198_);
v___x_292_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
v___x_293_ = l_Lean_mkIdent(v_binderName_197_);
v___x_294_ = l_Lean_MessageData_ofSyntax(v___x_293_);
v___x_295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_292_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_297_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
v___y_283_ = v_a_176_;
v___y_284_ = v_a_177_;
v___y_285_ = v_a_178_;
v___y_286_ = v_a_179_;
goto v___jp_282_;
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
v___x_273_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_272_, v___y_261_, v___y_258_, v___y_260_, v___y_259_);
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
uint8_t v___x_287_; 
v___x_287_ = lean_name_eq(v_binderName_197_, v_binderName_201_);
if (v___x_287_ == 0)
{
uint8_t v___x_288_; 
v___x_288_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_200_);
if (v___x_288_ == 0)
{
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
v___y_258_ = v___y_284_;
v___y_259_ = v___y_286_;
v___y_260_ = v___y_285_;
v___y_261_ = v___y_283_;
goto v___jp_257_;
}
else
{
uint8_t v___x_289_; 
v___x_289_ = l_Lean_Name_hasMacroScopes(v_binderName_197_);
if (v___x_289_ == 0)
{
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
v___y_258_ = v___y_284_;
v___y_259_ = v___y_286_;
v___y_260_ = v___y_285_;
v___y_261_ = v___y_283_;
goto v___jp_257_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = l_Lean_Name_hasMacroScopes(v_binderName_201_);
if (v___x_290_ == 0)
{
lean_dec_ref(v___f_205_);
lean_dec_ref(v_binderType_202_);
lean_dec_ref(v_binderType_198_);
v___y_258_ = v___y_284_;
v___y_259_ = v___y_286_;
v___y_260_ = v___y_285_;
v___y_261_ = v___y_283_;
goto v___jp_257_;
}
else
{
lean_dec(v_binderName_201_);
v___y_214_ = v___y_283_;
v___y_215_ = v___y_284_;
v___y_216_ = v___y_285_;
v___y_217_ = v___y_286_;
goto v___jp_213_;
}
}
}
}
else
{
lean_dec(v_binderName_201_);
v___y_214_ = v___y_283_;
v___y_215_ = v___y_284_;
v___y_216_ = v___y_285_;
v___y_217_ = v___y_286_;
goto v___jp_213_;
}
}
}
else
{
lean_dec_ref_known(v_a_194_, 3);
lean_dec(v_a_196_);
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
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_314_; 
lean_dec(v_a_194_);
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_k_171_);
v_a_307_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_314_ == 0)
{
v___x_309_ = v___x_195_;
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_195_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_314_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_n_192_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_x_174_);
lean_dec_ref(v_k_171_);
v_a_315_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_193_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_193_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object* v_body_323_, lean_object* v_body_324_, lean_object* v_x_325_, lean_object* v_k_326_, lean_object* v_n_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_334_ = lean_expr_instantiate1(v_body_323_, v_x_328_);
v___x_335_ = lean_expr_instantiate1(v_body_324_, v_x_328_);
v___x_336_ = lean_array_push(v_x_325_, v_x_328_);
v___x_337_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_326_, v_n_327_, v___x_334_, v___x_335_, v___x_336_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object* v_k_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_338_, v_x_339_, v_x_340_, v_x_341_, v_x_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_x_339_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object* v_00_u03b1_349_, lean_object* v_k_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_350_, v_x_351_, v_x_352_, v_x_353_, v_x_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object* v_00_u03b1_361_, lean_object* v_k_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_forallTelescopeCompatibleAux(v_00_u03b1_361_, v_k_362_, v_x_363_, v_x_364_, v_x_365_, v_x_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_x_363_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object* v_00_u03b1_373_, lean_object* v_msg_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object* v_00_u03b1_381_, lean_object* v_msg_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(v_00_u03b1_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object* v_k_389_, lean_object* v_runInBase_390_, lean_object* v_xs_391_, lean_object* v_type_u2081_392_, lean_object* v_type_u2082_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_apply_3(v_k_389_, v_xs_391_, v_type_u2081_392_, v_type_u2082_393_);
lean_inc(v___y_397_);
lean_inc_ref(v___y_396_);
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
v___x_400_ = lean_apply_7(v_runInBase_390_, lean_box(0), v___x_399_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, lean_box(0));
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object* v_k_401_, lean_object* v_runInBase_402_, lean_object* v_xs_403_, lean_object* v_type_u2081_404_, lean_object* v_type_u2082_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_401_, v_runInBase_402_, v_xs_403_, v_type_u2081_404_, v_type_u2082_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object* v_k_412_, lean_object* v_numParams_413_, lean_object* v_type_u2081_414_, lean_object* v_type_u2082_415_, lean_object* v_runInBase_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___f_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_422_, 0, v_k_412_);
lean_closure_set(v___f_422_, 1, v_runInBase_416_);
v___x_423_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_424_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v___f_422_, v_numParams_413_, v_type_u2081_414_, v_type_u2082_415_, v___x_423_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object* v_k_425_, lean_object* v_numParams_426_, lean_object* v_type_u2081_427_, lean_object* v_type_u2082_428_, lean_object* v_runInBase_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_425_, v_numParams_426_, v_type_u2081_427_, v_type_u2082_428_, v_runInBase_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v_numParams_426_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_type_u2081_438_, lean_object* v_type_u2082_439_, lean_object* v_numParams_440_, lean_object* v_k_441_){
_start:
{
lean_object* v_toBind_442_; lean_object* v_liftWith_443_; lean_object* v_restoreM_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_toBind_442_ = lean_ctor_get(v_inst_436_, 1);
lean_inc(v_toBind_442_);
lean_dec_ref(v_inst_436_);
v_liftWith_443_ = lean_ctor_get(v_inst_437_, 0);
lean_inc(v_liftWith_443_);
v_restoreM_444_ = lean_ctor_get(v_inst_437_, 1);
lean_inc(v_restoreM_444_);
lean_dec_ref(v_inst_437_);
v___f_445_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_445_, 0, v_k_441_);
lean_closure_set(v___f_445_, 1, v_numParams_440_);
lean_closure_set(v___f_445_, 2, v_type_u2081_438_);
lean_closure_set(v___f_445_, 3, v_type_u2082_439_);
v___x_446_ = lean_apply_2(v_liftWith_443_, lean_box(0), v___f_445_);
v___x_447_ = lean_apply_1(v_restoreM_444_, lean_box(0));
v___x_448_ = lean_apply_4(v_toBind_442_, lean_box(0), lean_box(0), v___x_446_, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object* v_m_449_, lean_object* v_00_u03b1_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_type_u2081_453_, lean_object* v_type_u2082_454_, lean_object* v_numParams_455_, lean_object* v_k_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_forallTelescopeCompatible___redArg(v_inst_451_, v_inst_452_, v_type_u2081_453_, v_type_u2082_454_, v_numParams_455_, v_k_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object* v_stx_458_){
_start:
{
lean_object* v___x_459_; lean_object* v_binders_460_; lean_object* v___x_461_; lean_object* v_optType_462_; uint8_t v___x_463_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v_binders_460_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_459_);
v___x_461_ = lean_unsigned_to_nat(1u);
v_optType_462_ = l_Lean_Syntax_getArg(v_stx_458_, v___x_461_);
v___x_463_ = l_Lean_Syntax_isNone(v_optType_462_);
if (v___x_463_ == 0)
{
lean_object* v_typeSpec_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_typeSpec_464_ = l_Lean_Syntax_getArg(v_optType_462_, v___x_459_);
lean_dec(v_optType_462_);
v___x_465_ = l_Lean_Syntax_getArg(v_typeSpec_464_, v___x_461_);
lean_dec(v_typeSpec_464_);
v___x_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_binders_460_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v_optType_462_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_469_, 0, v_binders_460_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object* v_stx_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Elab_expandOptDeclSig(v_stx_470_);
lean_dec(v_stx_470_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object* v_stx_472_){
_start:
{
lean_object* v___x_473_; lean_object* v_binders_474_; lean_object* v___x_475_; lean_object* v_typeSpec_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v_binders_474_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_473_);
v___x_475_ = lean_unsigned_to_nat(1u);
v_typeSpec_476_ = l_Lean_Syntax_getArg(v_stx_472_, v___x_475_);
v___x_477_ = l_Lean_Syntax_getArg(v_typeSpec_476_, v___x_475_);
lean_dec(v_typeSpec_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_binders_474_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object* v_stx_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Elab_expandDeclSig(v_stx_479_);
lean_dec(v_stx_479_);
return v_res_480_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object* v_a_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
else
{
lean_object* v_head_484_; lean_object* v_tail_485_; uint8_t v___x_486_; 
v_head_484_ = lean_ctor_get(v_x_482_, 0);
v_tail_485_ = lean_ctor_get(v_x_482_, 1);
v___x_486_ = lean_name_eq(v_a_481_, v_head_484_);
if (v___x_486_ == 0)
{
v_x_482_ = v_tail_485_;
goto _start;
}
else
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
uint8_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec(v_a_488_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object* v_allUserParams_492_, lean_object* v_as_493_, size_t v_i_494_, size_t v_stop_495_, lean_object* v_b_496_){
_start:
{
lean_object* v___y_498_; uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_eq(v_i_494_, v_stop_495_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_uget_borrowed(v_as_493_, v_i_494_);
v___x_504_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v___x_503_, v_allUserParams_492_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_inc(v___x_503_);
v___x_505_ = lean_array_push(v_b_496_, v___x_503_);
v___y_498_ = v___x_505_;
goto v___jp_497_;
}
else
{
v___y_498_ = v_b_496_;
goto v___jp_497_;
}
}
else
{
return v_b_496_;
}
v___jp_497_:
{
size_t v___x_499_; size_t v___x_500_; 
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_494_, v___x_499_);
v_i_494_ = v___x_500_;
v_b_496_ = v___y_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object* v_allUserParams_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_stop_509_, lean_object* v_b_510_){
_start:
{
size_t v_i_boxed_511_; size_t v_stop_boxed_512_; lean_object* v_res_513_; 
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_stop_boxed_512_ = lean_unbox_usize(v_stop_509_);
lean_dec(v_stop_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_506_, v_as_507_, v_i_boxed_511_, v_stop_boxed_512_, v_b_510_);
lean_dec_ref(v_as_507_);
lean_dec(v_allUserParams_506_);
return v_res_513_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object* v_a_514_, lean_object* v_as_515_, size_t v_i_516_, size_t v_stop_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_eq(v_i_516_, v_stop_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_uget_borrowed(v_as_515_, v_i_516_);
v___x_520_ = lean_name_eq(v_a_514_, v___x_519_);
if (v___x_520_ == 0)
{
size_t v___x_521_; size_t v___x_522_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_516_, v___x_521_);
v_i_516_ = v___x_522_;
goto _start;
}
else
{
return v___x_520_;
}
}
else
{
uint8_t v___x_524_; 
v___x_524_ = 0;
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object* v_a_525_, lean_object* v_as_526_, lean_object* v_i_527_, lean_object* v_stop_528_){
_start:
{
size_t v_i_boxed_529_; size_t v_stop_boxed_530_; uint8_t v_res_531_; lean_object* v_r_532_; 
v_i_boxed_529_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_stop_boxed_530_ = lean_unbox_usize(v_stop_528_);
lean_dec(v_stop_528_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_525_, v_as_526_, v_i_boxed_529_, v_stop_boxed_530_);
lean_dec_ref(v_as_526_);
lean_dec(v_a_525_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object* v_as_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_array_get_size(v_as_533_);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
return v___x_537_;
}
else
{
size_t v___x_538_; size_t v___x_539_; uint8_t v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_534_, v_as_533_, v___x_538_, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object* v_as_541_, lean_object* v_a_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_as_541_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object* v_usedParams_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
return v_x_546_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_head_548_ = lean_ctor_get(v_x_547_, 0);
v_tail_549_ = lean_ctor_get(v_x_547_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___x_553_; 
v___x_553_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_545_, v_head_548_);
if (v___x_553_ == 0)
{
lean_del_object(v___x_551_);
lean_dec(v_head_548_);
v_x_547_ = v_tail_549_;
goto _start;
}
else
{
lean_object* v___x_556_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 1, v_x_546_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_head_548_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_x_546_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
v_x_546_ = v___x_556_;
v_x_547_ = v_tail_549_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object* v_usedParams_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_560_, v_x_561_, v_x_562_);
lean_dec_ref(v_usedParams_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object* v_usedParams_564_, lean_object* v_scopeParams_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_567_; 
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v_head_568_; lean_object* v_tail_569_; uint8_t v___x_570_; 
v_head_568_ = lean_ctor_get(v_x_566_, 0);
v_tail_569_ = lean_ctor_get(v_x_566_, 1);
v___x_570_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_564_, v_head_568_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; 
v___x_571_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_head_568_, v_scopeParams_565_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; 
lean_inc(v_head_568_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_head_568_);
return v___x_572_;
}
else
{
v_x_566_ = v_tail_569_;
goto _start;
}
}
else
{
v_x_566_ = v_tail_569_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object* v_usedParams_575_, lean_object* v_scopeParams_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_575_, v_scopeParams_576_, v_x_577_);
lean_dec(v_x_577_);
lean_dec(v_scopeParams_576_);
lean_dec_ref(v_usedParams_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object* v_hi_579_, lean_object* v_pivot_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_k_583_){
_start:
{
uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_lt(v_k_583_, v_hi_579_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_k_583_);
v___x_585_ = lean_array_fswap(v_as_581_, v_i_582_, v_hi_579_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_i_582_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_array_fget_borrowed(v_as_581_, v_k_583_);
v___x_588_ = l_Lean_Name_lt(v___x_587_, v_pivot_580_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_k_583_, v___x_589_);
lean_dec(v_k_583_);
v_k_583_ = v___x_590_;
goto _start;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_592_ = lean_array_fswap(v_as_581_, v_i_582_, v_k_583_);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = lean_nat_add(v_i_582_, v___x_593_);
lean_dec(v_i_582_);
v___x_595_ = lean_nat_add(v_k_583_, v___x_593_);
lean_dec(v_k_583_);
v_as_581_ = v___x_592_;
v_i_582_ = v___x_594_;
v_k_583_ = v___x_595_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object* v_hi_597_, lean_object* v_pivot_598_, lean_object* v_as_599_, lean_object* v_i_600_, lean_object* v_k_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_597_, v_pivot_598_, v_as_599_, v_i_600_, v_k_601_);
lean_dec(v_pivot_598_);
lean_dec(v_hi_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object* v_n_603_, lean_object* v_as_604_, lean_object* v_lo_605_, lean_object* v_hi_606_){
_start:
{
lean_object* v___y_608_; uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v_lo_605_, v_hi_606_);
if (v___x_618_ == 0)
{
lean_dec(v_lo_605_);
return v_as_604_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v_mid_621_; lean_object* v___y_623_; lean_object* v___y_629_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_619_ = lean_nat_add(v_lo_605_, v_hi_606_);
v___x_620_ = lean_unsigned_to_nat(1u);
v_mid_621_ = lean_nat_shiftr(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v___x_634_ = lean_array_fget_borrowed(v_as_604_, v_mid_621_);
v___x_635_ = lean_array_fget_borrowed(v_as_604_, v_lo_605_);
v___x_636_ = l_Lean_Name_lt(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
v___y_629_ = v_as_604_;
goto v___jp_628_;
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_array_fswap(v_as_604_, v_lo_605_, v_mid_621_);
v___y_629_ = v___x_637_;
goto v___jp_628_;
}
v___jp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_array_fget_borrowed(v___y_623_, v_mid_621_);
v___x_625_ = lean_array_fget_borrowed(v___y_623_, v_hi_606_);
v___x_626_ = l_Lean_Name_lt(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v_mid_621_);
v___y_608_ = v___y_623_;
goto v___jp_607_;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_array_fswap(v___y_623_, v_mid_621_, v_hi_606_);
lean_dec(v_mid_621_);
v___y_608_ = v___x_627_;
goto v___jp_607_;
}
}
v___jp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_array_fget_borrowed(v___y_629_, v_hi_606_);
v___x_631_ = lean_array_fget_borrowed(v___y_629_, v_lo_605_);
v___x_632_ = l_Lean_Name_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
v___y_623_ = v___y_629_;
goto v___jp_622_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = lean_array_fswap(v___y_629_, v_lo_605_, v_hi_606_);
v___y_623_ = v___x_633_;
goto v___jp_622_;
}
}
}
v___jp_607_:
{
lean_object* v_pivot_609_; lean_object* v___x_610_; lean_object* v_fst_611_; lean_object* v_snd_612_; uint8_t v___x_613_; 
v_pivot_609_ = lean_array_fget(v___y_608_, v_hi_606_);
lean_inc_n(v_lo_605_, 2);
v___x_610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_606_, v_pivot_609_, v___y_608_, v_lo_605_, v_lo_605_);
lean_dec(v_pivot_609_);
v_fst_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_fst_611_);
v_snd_612_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_snd_612_);
lean_dec_ref(v___x_610_);
v___x_613_ = lean_nat_dec_le(v_hi_606_, v_fst_611_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_603_, v_snd_612_, v_lo_605_, v_fst_611_);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_fst_611_, v___x_615_);
lean_dec(v_fst_611_);
v_as_604_ = v___x_614_;
v_lo_605_ = v___x_616_;
goto _start;
}
else
{
lean_dec(v_fst_611_);
lean_dec(v_lo_605_);
return v_snd_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object* v_n_638_, lean_object* v_as_639_, lean_object* v_lo_640_, lean_object* v_hi_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_638_, v_as_639_, v_lo_640_, v_hi_641_);
lean_dec(v_hi_641_);
lean_dec(v_n_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object* v_scopeParams_647_, lean_object* v_allUserParams_648_, lean_object* v_usedParams_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_649_, v_scopeParams_647_, v_allUserParams_648_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_651_; lean_object* v_result_652_; lean_object* v___y_654_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_670_; lean_object* v___y_672_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_651_ = lean_box(0);
lean_inc(v_allUserParams_648_);
v_result_652_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_649_, v___x_651_, v_allUserParams_648_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_size(v_usedParams_649_);
v___x_679_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__0));
v___x_680_ = lean_nat_dec_lt(v___x_670_, v___x_678_);
if (v___x_680_ == 0)
{
lean_dec(v_allUserParams_648_);
v___y_672_ = v___x_679_;
goto v___jp_671_;
}
else
{
size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_usize_of_nat(v___x_678_);
v___x_683_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_648_, v_usedParams_649_, v___x_681_, v___x_682_, v___x_679_);
lean_dec(v_allUserParams_648_);
v___y_672_ = v___x_683_;
goto v___jp_671_;
}
v___jp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_array_to_list(v___y_654_);
v___x_656_ = l_List_appendTR___redArg(v_result_652_, v___x_655_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
v___jp_658_:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_660_, v___y_659_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec(v___y_660_);
v___y_654_ = v___x_663_;
goto v___jp_653_;
}
v___jp_664_:
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_le(v___y_668_, v___y_667_);
if (v___x_669_ == 0)
{
lean_dec(v___y_667_);
lean_inc(v___y_668_);
v___y_659_ = v___y_665_;
v___y_660_ = v___y_666_;
v___y_661_ = v___y_668_;
v___y_662_ = v___y_668_;
goto v___jp_658_;
}
else
{
v___y_659_ = v___y_665_;
v___y_660_ = v___y_666_;
v___y_661_ = v___y_668_;
v___y_662_ = v___y_667_;
goto v___jp_658_;
}
}
v___jp_671_:
{
lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_673_ = lean_array_get_size(v___y_672_);
v___x_674_ = lean_nat_dec_eq(v___x_673_, v___x_670_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_sub(v___x_673_, v___x_675_);
v___x_677_ = lean_nat_dec_le(v___x_670_, v___x_676_);
if (v___x_677_ == 0)
{
lean_inc(v___x_676_);
v___y_665_ = v___y_672_;
v___y_666_ = v___x_673_;
v___y_667_ = v___x_676_;
v___y_668_ = v___x_676_;
goto v___jp_664_;
}
else
{
v___y_665_ = v___y_672_;
v___y_666_ = v___x_673_;
v___y_667_ = v___x_676_;
v___y_668_ = v___x_670_;
goto v___jp_664_;
}
}
else
{
v___y_654_ = v___y_672_;
goto v___jp_653_;
}
}
}
else
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_allUserParams_648_);
v_val_684_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_697_ == 0)
{
v___x_686_ = v___x_650_;
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_650_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_697_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_688_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__1));
v___x_689_ = 1;
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_684_, v___x_689_);
v___x_691_ = lean_string_append(v___x_688_, v___x_690_);
lean_dec_ref(v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__2));
v___x_693_ = lean_string_append(v___x_691_, v___x_692_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 0);
lean_ctor_set(v___x_686_, 0, v___x_693_);
v___x_695_ = v___x_686_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object* v_scopeParams_698_, lean_object* v_allUserParams_699_, lean_object* v_usedParams_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_sortDeclLevelParams(v_scopeParams_698_, v_allUserParams_699_, v_usedParams_700_);
lean_dec_ref(v_usedParams_700_);
lean_dec(v_scopeParams_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object* v_n_702_, lean_object* v_as_703_, lean_object* v_lo_704_, lean_object* v_hi_705_, lean_object* v_w_706_, lean_object* v_hlo_707_, lean_object* v_hhi_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_702_, v_as_703_, v_lo_704_, v_hi_705_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object* v_n_710_, lean_object* v_as_711_, lean_object* v_lo_712_, lean_object* v_hi_713_, lean_object* v_w_714_, lean_object* v_hlo_715_, lean_object* v_hhi_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_710_, v_as_711_, v_lo_712_, v_hi_713_, v_w_714_, v_hlo_715_, v_hhi_716_);
lean_dec(v_hi_713_);
lean_dec(v_n_710_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object* v_n_718_, lean_object* v_lo_719_, lean_object* v_hi_720_, lean_object* v_hhi_721_, lean_object* v_pivot_722_, lean_object* v_as_723_, lean_object* v_i_724_, lean_object* v_k_725_, lean_object* v_ilo_726_, lean_object* v_ik_727_, lean_object* v_w_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_720_, v_pivot_722_, v_as_723_, v_i_724_, v_k_725_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object* v_n_730_, lean_object* v_lo_731_, lean_object* v_hi_732_, lean_object* v_hhi_733_, lean_object* v_pivot_734_, lean_object* v_as_735_, lean_object* v_i_736_, lean_object* v_k_737_, lean_object* v_ilo_738_, lean_object* v_ik_739_, lean_object* v_w_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_730_, v_lo_731_, v_hi_732_, v_hhi_733_, v_pivot_734_, v_as_735_, v_i_736_, v_k_737_, v_ilo_738_, v_ik_739_, v_w_740_);
lean_dec(v_pivot_734_);
lean_dec(v_hi_732_);
lean_dec(v_lo_731_);
lean_dec(v_n_730_);
return v_res_741_;
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
