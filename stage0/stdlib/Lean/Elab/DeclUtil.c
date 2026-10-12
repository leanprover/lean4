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
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_9_;
v_res_9_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(v_k_1_, v_b_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
lean_dec(v___y_13_);
lean_dec_ref(v___y_12_);
return v_res_17_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(lean_object* v_name_18_, uint8_t v_bi_19_, lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_kind_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_18_, v_bi_19_, v_type_20_, v___f_28_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_29_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_29_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_29_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_29_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_18_ = stack[0].m_obj;
uint8_t v_bi_19_ = stack[1].m_num;
lean_object* v_type_20_ = stack[2].m_obj;
lean_object* v_k_21_ = stack[3].m_obj;
uint8_t v_kind_22_ = stack[4].m_num;
lean_object* v___y_23_ = stack[5].m_obj;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v___y_25_ = stack[7].m_obj;
lean_object* v___y_26_ = stack[8].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_name_18_, v_bi_19_, v_type_20_, v_k_21_, v_kind_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___boxed(lean_object* v_name_47_, lean_object* v_bi_48_, lean_object* v_type_49_, lean_object* v_k_50_, lean_object* v_kind_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_bi_boxed_57_; uint8_t v_kind_boxed_58_; lean_object* v_res_59_; 
v_bi_boxed_57_ = lean_unbox(v_bi_48_);
v_kind_boxed_58_ = lean_unbox(v_kind_51_);
v_res_59_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_name_47_, v_bi_boxed_57_, v_type_49_, v_k_50_, v_kind_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_name_61_, uint8_t v_bi_62_, lean_object* v_type_63_, lean_object* v_k_64_, uint8_t v_kind_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_61_ = stack[1].m_obj;
uint8_t v_bi_62_ = stack[2].m_num;
lean_object* v_type_63_ = stack[3].m_obj;
lean_object* v_k_64_ = stack[4].m_obj;
uint8_t v_kind_65_ = stack[5].m_num;
lean_object* v___y_66_ = stack[6].m_obj;
lean_object* v___y_67_ = stack[7].m_obj;
lean_object* v___y_68_ = stack[8].m_obj;
lean_object* v___y_69_ = stack[9].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(lean_box(0), v_name_61_, v_bi_62_, v_type_63_, v_k_64_, v_kind_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___boxed(lean_object* v_00_u03b1_73_, lean_object* v_name_74_, lean_object* v_bi_75_, lean_object* v_type_76_, lean_object* v_k_77_, lean_object* v_kind_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
uint8_t v_bi_boxed_84_; uint8_t v_kind_boxed_85_; lean_object* v_res_86_; 
v_bi_boxed_84_ = lean_unbox(v_bi_75_);
v_kind_boxed_85_ = lean_unbox(v_kind_78_);
v_res_86_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(v_00_u03b1_73_, v_name_74_, v_bi_boxed_84_, v_type_76_, v_k_77_, v_kind_boxed_85_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_86_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(lean_object* v_msgData_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_env_94_; uint8_t v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v_toCold_98_; lean_object* v_mctx_99_; lean_object* v_lctx_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = 0;
v_env_96_ = l_Lean_Environment_setRecordingDeps(v_env_94_, v___x_95_);
v___x_97_ = lean_st_ref_get(v___y_89_);
v_toCold_98_ = lean_ctor_get(v___y_90_, 0);
v_mctx_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_mctx_99_);
lean_dec(v___x_97_);
v_lctx_100_ = lean_ctor_get(v___y_88_, 2);
v_options_101_ = lean_ctor_get(v_toCold_98_, 2);
lean_inc_ref(v_options_101_);
lean_inc_ref(v_lctx_100_);
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v_env_96_);
lean_ctor_set(v___x_102_, 1, v_mctx_99_);
lean_ctor_set(v___x_102_, 2, v_lctx_100_);
lean_ctor_set(v___x_102_, 3, v_options_101_);
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_msgData_87_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_87_ = stack[0].m_obj;
lean_object* v___y_88_ = stack[1].m_obj;
lean_object* v___y_89_ = stack[2].m_obj;
lean_object* v___y_90_ = stack[3].m_obj;
lean_object* v___y_91_ = stack[4].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 2);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_113_ = stack[0].m_obj;
lean_object* v___y_114_ = stack[1].m_obj;
lean_object* v___y_115_ = stack[2].m_obj;
lean_object* v___y_116_ = stack[3].m_obj;
lean_object* v___y_117_ = stack[4].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_137_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0));
v___x_140_ = l_Lean_stringToMessageData(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(lean_object* v_body_141_, lean_object* v_body_142_, lean_object* v_x_143_, lean_object* v_k_144_, lean_object* v_n_145_, lean_object* v_x_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(v_body_141_, v_body_142_, v_x_143_, v_k_144_, v_n_145_, v_x_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v_n_145_);
lean_dec_ref(v_body_142_);
lean_dec_ref(v_body_141_);
return v_res_152_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3));
v___x_157_ = l_Lean_stringToMessageData(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5));
v___x_160_ = l_Lean_stringToMessageData(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7));
v___x_163_ = l_Lean_stringToMessageData(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9));
v___x_166_ = l_Lean_stringToMessageData(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15));
v___x_175_ = l_Lean_stringToMessageData(v___x_174_);
return v___x_175_;
}
}
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg(lean_object* v_k_176_, lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; lean_object* v_zero_193_; uint8_t v_isZero_194_; 
v_zero_193_ = lean_unsigned_to_nat(0u);
v_isZero_194_ = lean_nat_dec_eq(v_x_177_, v_zero_193_);
if (v_isZero_194_ == 1)
{
lean_object* v___x_195_; 
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
v___x_195_ = lean_apply_8(v_k_176_, v_x_180_, v_x_178_, v_x_179_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v_one_196_; lean_object* v_n_197_; lean_object* v___x_198_; 
v_one_196_ = lean_unsigned_to_nat(1u);
v_n_197_ = lean_nat_sub(v_x_177_, v_one_196_);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
v___x_198_ = lean_whnf(v_x_178_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
lean_inc(v_a_184_);
lean_inc_ref(v_a_183_);
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
v___x_200_ = lean_whnf(v_x_179_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
if (lean_obj_tag(v___x_200_) == 0)
{
if (lean_obj_tag(v_a_199_) == 7)
{
lean_object* v_a_201_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
if (lean_obj_tag(v_a_201_) == 7)
{
lean_object* v_binderName_202_; lean_object* v_binderType_203_; lean_object* v_body_204_; uint8_t v_binderInfo_205_; lean_object* v_binderName_206_; lean_object* v_binderType_207_; lean_object* v_body_208_; uint8_t v_binderInfo_209_; lean_object* v___f_210_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_292_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; lean_object* v___y_297_; uint8_t v___y_298_; lean_object* v___y_301_; lean_object* v___y_302_; lean_object* v___y_303_; lean_object* v___y_304_; uint8_t v___x_308_; 
v_binderName_202_ = lean_ctor_get(v_a_199_, 0);
lean_inc(v_binderName_202_);
v_binderType_203_ = lean_ctor_get(v_a_199_, 1);
lean_inc_ref(v_binderType_203_);
v_body_204_ = lean_ctor_get(v_a_199_, 2);
lean_inc_ref(v_body_204_);
v_binderInfo_205_ = lean_ctor_get_uint8(v_a_199_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_199_, 3);
v_binderName_206_ = lean_ctor_get(v_a_201_, 0);
lean_inc(v_binderName_206_);
v_binderType_207_ = lean_ctor_get(v_a_201_, 1);
lean_inc_ref(v_binderType_207_);
v_body_208_ = lean_ctor_get(v_a_201_, 2);
lean_inc_ref(v_body_208_);
v_binderInfo_209_ = lean_ctor_get_uint8(v_a_201_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_201_, 3);
v___f_210_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_210_, 0, v_body_204_);
lean_closure_set(v___f_210_, 1, v_body_208_);
lean_closure_set(v___f_210_, 2, v_x_180_);
lean_closure_set(v___f_210_, 3, v_k_176_);
lean_closure_set(v___f_210_, 4, v_n_197_);
v___x_308_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_205_, v_binderInfo_209_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v___f_210_);
lean_dec_ref(v_binderType_207_);
lean_dec(v_binderName_206_);
lean_dec_ref(v_binderType_203_);
v___x_309_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
v___x_310_ = l_Lean_mkIdent(v_binderName_202_);
v___x_311_ = l_Lean_MessageData_ofSyntax(v___x_310_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_309_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_314_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
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
else
{
v___y_301_ = v_a_181_;
v___y_302_ = v_a_182_;
v___y_303_ = v_a_183_;
v___y_304_ = v_a_184_;
goto v___jp_300_;
}
v___jp_211_:
{
uint8_t v___x_216_; lean_object* v___x_217_; 
v___x_216_ = 0;
v___x_217_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_binderName_202_, v_binderInfo_205_, v_binderType_203_, v___f_210_, v___x_216_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v___x_217_;
}
v___jp_218_:
{
lean_object* v___x_223_; 
lean_inc_ref(v_binderType_207_);
lean_inc_ref(v_binderType_203_);
v___x_223_ = l_Lean_Meta_isExprDefEq(v_binderType_203_, v_binderType_207_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; uint8_t v___x_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = lean_unbox(v_a_224_);
lean_dec(v_a_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v___f_210_);
v___x_226_ = lean_box(0);
v___x_227_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_228_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_binderType_203_, v_binderType_207_, v___x_226_, v___x_227_, v___y_219_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4);
v___x_231_ = l_Lean_mkIdent(v_binderName_202_);
v___x_232_ = l_Lean_MessageData_ofSyntax(v___x_231_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_230_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_229_);
v___x_237_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_236_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
v_a_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_237_);
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
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec(v_binderName_202_);
v_a_246_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_228_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_228_);
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
else
{
lean_dec_ref(v_binderType_207_);
v___y_212_ = v___y_219_;
v___y_213_ = v___y_220_;
v___y_214_ = v___y_221_;
v___y_215_ = v___y_222_;
goto v___jp_211_;
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v___f_210_);
lean_dec_ref(v_binderType_207_);
lean_dec_ref(v_binderType_203_);
lean_dec(v_binderName_202_);
v_a_254_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_223_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_223_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
v___jp_262_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v___x_267_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8);
v___x_268_ = l_Lean_mkIdent(v_binderName_202_);
v___x_269_ = l_Lean_MessageData_ofSyntax(v___x_268_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_267_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_mkIdent(v_binderName_206_);
v___x_274_ = l_Lean_MessageData_ofSyntax(v___x_273_);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_272_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_277_, v___y_265_, v___y_264_, v___y_266_, v___y_263_);
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
v___jp_287_:
{
if (v___y_292_ == 0)
{
lean_dec_ref(v___f_210_);
lean_dec_ref(v_binderType_207_);
lean_dec_ref(v_binderType_203_);
v___y_263_ = v___y_289_;
v___y_264_ = v___y_288_;
v___y_265_ = v___y_290_;
v___y_266_ = v___y_291_;
goto v___jp_262_;
}
else
{
lean_dec(v_binderName_206_);
v___y_219_ = v___y_290_;
v___y_220_ = v___y_288_;
v___y_221_ = v___y_291_;
v___y_222_ = v___y_289_;
goto v___jp_218_;
}
}
v___jp_293_:
{
if (v___y_298_ == 0)
{
lean_dec_ref(v___f_210_);
lean_dec_ref(v_binderType_207_);
lean_dec_ref(v_binderType_203_);
v___y_263_ = v___y_295_;
v___y_264_ = v___y_294_;
v___y_265_ = v___y_296_;
v___y_266_ = v___y_297_;
goto v___jp_262_;
}
else
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Name_hasMacroScopes(v_binderName_206_);
v___y_288_ = v___y_294_;
v___y_289_ = v___y_295_;
v___y_290_ = v___y_296_;
v___y_291_ = v___y_297_;
v___y_292_ = v___x_299_;
goto v___jp_287_;
}
}
v___jp_300_:
{
uint8_t v___x_305_; 
v___x_305_ = lean_name_eq(v_binderName_202_, v_binderName_206_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_205_);
if (v___x_306_ == 0)
{
v___y_294_ = v___y_302_;
v___y_295_ = v___y_304_;
v___y_296_ = v___y_301_;
v___y_297_ = v___y_303_;
v___y_298_ = v___x_306_;
goto v___jp_293_;
}
else
{
uint8_t v___x_307_; 
v___x_307_ = l_Lean_Name_hasMacroScopes(v_binderName_202_);
v___y_294_ = v___y_302_;
v___y_295_ = v___y_304_;
v___y_296_ = v___y_301_;
v___y_297_ = v___y_303_;
v___y_298_ = v___x_307_;
goto v___jp_293_;
}
}
else
{
v___y_288_ = v___y_302_;
v___y_289_ = v___y_304_;
v___y_290_ = v___y_301_;
v___y_291_ = v___y_303_;
v___y_292_ = v___x_305_;
goto v___jp_287_;
}
}
}
else
{
lean_dec_ref_known(v_a_199_, 3);
lean_dec(v_a_201_);
lean_dec(v_n_197_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_k_176_);
v___y_187_ = v_a_181_;
v___y_188_ = v_a_182_;
v___y_189_ = v_a_183_;
v___y_190_ = v_a_184_;
goto v___jp_186_;
}
}
else
{
lean_dec_ref_known(v___x_200_, 1);
lean_dec(v_a_199_);
lean_dec(v_n_197_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_k_176_);
v___y_187_ = v_a_181_;
v___y_188_ = v_a_182_;
v___y_189_ = v_a_183_;
v___y_190_ = v_a_184_;
goto v___jp_186_;
}
}
else
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
lean_dec(v_a_199_);
lean_dec(v_n_197_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_k_176_);
v_a_324_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___x_200_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_200_);
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
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
lean_dec(v_n_197_);
lean_dec_ref(v_x_180_);
lean_dec_ref(v_x_179_);
lean_dec_ref(v_k_176_);
v_a_332_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_198_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_198_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
v___jp_186_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_obj_once(&l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1, &l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once, _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1);
v___x_192_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_191_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
return v___x_192_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeCompatibleAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_176_ = stack[0].m_obj;
lean_object* v_x_177_ = stack[1].m_obj;
lean_object* v_x_178_ = stack[2].m_obj;
lean_object* v_x_179_ = stack[3].m_obj;
lean_object* v_x_180_ = stack[4].m_obj;
lean_object* v_a_181_ = stack[5].m_obj;
lean_object* v_a_182_ = stack[6].m_obj;
lean_object* v_a_183_ = stack[7].m_obj;
lean_object* v_a_184_ = stack[8].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_176_, v_x_177_, v_x_178_, v_x_179_, v_x_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
stack->m_obj
 = v_res_340_;
}
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(lean_object* v_body_341_, lean_object* v_body_342_, lean_object* v_x_343_, lean_object* v_k_344_, lean_object* v_n_345_, lean_object* v_x_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_expr_instantiate1(v_body_341_, v_x_346_);
v___x_353_ = lean_expr_instantiate1(v_body_342_, v_x_346_);
v___x_354_ = lean_array_push(v_x_343_, v_x_346_);
v___x_355_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_344_, v_n_345_, v___x_352_, v___x_353_, v___x_354_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_355_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_341_ = stack[0].m_obj;
lean_object* v_body_342_ = stack[1].m_obj;
lean_object* v_x_343_ = stack[2].m_obj;
lean_object* v_k_344_ = stack[3].m_obj;
lean_object* v_n_345_ = stack[4].m_obj;
lean_object* v_x_346_ = stack[5].m_obj;
lean_object* v___y_347_ = stack[6].m_obj;
lean_object* v___y_348_ = stack[7].m_obj;
lean_object* v___y_349_ = stack[8].m_obj;
lean_object* v___y_350_ = stack[9].m_obj;
lean_object* v_res_356_;
v_res_356_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(v_body_341_, v_body_342_, v_x_343_, v_k_344_, v_n_345_, v_x_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
stack->m_obj
 = v_res_356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(lean_object* v_k_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_357_, v_x_358_, v_x_359_, v_x_360_, v_x_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_x_358_);
return v_res_367_;
}
}
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux(lean_object* v_00_u03b1_368_, lean_object* v_k_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v_k_369_, v_x_370_, v_x_371_, v_x_372_, v_x_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeCompatibleAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_369_ = stack[1].m_obj;
lean_object* v_x_370_ = stack[2].m_obj;
lean_object* v_x_371_ = stack[3].m_obj;
lean_object* v_x_372_ = stack[4].m_obj;
lean_object* v_x_373_ = stack[5].m_obj;
lean_object* v_a_374_ = stack[6].m_obj;
lean_object* v_a_375_ = stack[7].m_obj;
lean_object* v_a_376_ = stack[8].m_obj;
lean_object* v_a_377_ = stack[9].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Meta_forallTelescopeCompatibleAux(lean_box(0), v_k_369_, v_x_370_, v_x_371_, v_x_372_, v_x_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___boxed(lean_object* v_00_u03b1_381_, lean_object* v_k_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_forallTelescopeCompatibleAux(v_00_u03b1_381_, v_k_382_, v_x_383_, v_x_384_, v_x_385_, v_x_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_x_383_);
return v_res_392_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_object* v_00_u03b1_393_, lean_object* v_msg_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v___x_400_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_394_ = stack[1].m_obj;
lean_object* v___y_395_ = stack[2].m_obj;
lean_object* v___y_396_ = stack[3].m_obj;
lean_object* v___y_397_ = stack[4].m_obj;
lean_object* v___y_398_ = stack[5].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(lean_box(0), v_msg_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(v_00_u03b1_402_, v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(lean_object* v_k_410_, lean_object* v_runInBase_411_, lean_object* v_xs_412_, lean_object* v_type_u2081_413_, lean_object* v_type_u2082_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_apply_3(v_k_410_, v_xs_412_, v_type_u2081_413_, v_type_u2082_414_);
lean_inc(v___y_418_);
lean_inc_ref(v___y_417_);
lean_inc(v___y_416_);
lean_inc_ref(v___y_415_);
v___x_421_ = lean_apply_7(v_runInBase_411_, lean_box(0), v___x_420_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, lean_box(0));
return v___x_421_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_410_ = stack[0].m_obj;
lean_object* v_runInBase_411_ = stack[1].m_obj;
lean_object* v_xs_412_ = stack[2].m_obj;
lean_object* v_type_u2081_413_ = stack[3].m_obj;
lean_object* v_type_u2082_414_ = stack[4].m_obj;
lean_object* v___y_415_ = stack[5].m_obj;
lean_object* v___y_416_ = stack[6].m_obj;
lean_object* v___y_417_ = stack[7].m_obj;
lean_object* v___y_418_ = stack[8].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_410_, v_runInBase_411_, v_xs_412_, v_type_u2081_413_, v_type_u2082_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(lean_object* v_k_423_, lean_object* v_runInBase_424_, lean_object* v_xs_425_, lean_object* v_type_u2081_426_, lean_object* v_type_u2082_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(v_k_423_, v_runInBase_424_, v_xs_425_, v_type_u2081_426_, v_type_u2082_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_433_;
}
}
lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(lean_object* v_k_434_, lean_object* v_numParams_435_, lean_object* v_type_u2081_436_, lean_object* v_type_u2082_437_, lean_object* v_runInBase_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___f_444_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed), 10, 2);
lean_closure_set(v___f_444_, 0, v_k_434_);
lean_closure_set(v___f_444_, 1, v_runInBase_438_);
v___x_445_ = ((lean_object*)(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2));
v___x_446_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(v___f_444_, v_numParams_435_, v_type_u2081_436_, v_type_u2082_437_, v___x_445_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_434_ = stack[0].m_obj;
lean_object* v_numParams_435_ = stack[1].m_obj;
lean_object* v_type_u2081_436_ = stack[2].m_obj;
lean_object* v_type_u2082_437_ = stack[3].m_obj;
lean_object* v_runInBase_438_ = stack[4].m_obj;
lean_object* v___y_439_ = stack[5].m_obj;
lean_object* v___y_440_ = stack[6].m_obj;
lean_object* v___y_441_ = stack[7].m_obj;
lean_object* v___y_442_ = stack[8].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_434_, v_numParams_435_, v_type_u2081_436_, v_type_u2082_437_, v_runInBase_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(lean_object* v_k_448_, lean_object* v_numParams_449_, lean_object* v_type_u2081_450_, lean_object* v_type_u2082_451_, lean_object* v_runInBase_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(v_k_448_, v_numParams_449_, v_type_u2081_450_, v_type_u2082_451_, v_runInBase_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v_numParams_449_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___redArg(lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_type_u2081_461_, lean_object* v_type_u2082_462_, lean_object* v_numParams_463_, lean_object* v_k_464_){
_start:
{
lean_object* v_toBind_465_; lean_object* v_liftWith_466_; lean_object* v_restoreM_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_toBind_465_ = lean_ctor_get(v_inst_459_, 1);
lean_inc(v_toBind_465_);
lean_dec_ref(v_inst_459_);
v_liftWith_466_ = lean_ctor_get(v_inst_460_, 0);
lean_inc(v_liftWith_466_);
v_restoreM_467_ = lean_ctor_get(v_inst_460_, 1);
lean_inc(v_restoreM_467_);
lean_dec_ref(v_inst_460_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_468_, 0, v_k_464_);
lean_closure_set(v___f_468_, 1, v_numParams_463_);
lean_closure_set(v___f_468_, 2, v_type_u2081_461_);
lean_closure_set(v___f_468_, 3, v_type_u2082_462_);
v___x_469_ = lean_apply_2(v_liftWith_466_, lean_box(0), v___f_468_);
v___x_470_ = lean_apply_1(v_restoreM_467_, lean_box(0));
v___x_471_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_469_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible(lean_object* v_m_472_, lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_type_u2081_476_, lean_object* v_type_u2082_477_, lean_object* v_numParams_478_, lean_object* v_k_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_forallTelescopeCompatible___redArg(v_inst_474_, v_inst_475_, v_type_u2081_476_, v_type_u2082_477_, v_numParams_478_, v_k_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig(lean_object* v_stx_481_){
_start:
{
lean_object* v___x_482_; lean_object* v_binders_483_; lean_object* v___x_484_; lean_object* v_optType_485_; uint8_t v___x_486_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v_binders_483_ = l_Lean_Syntax_getArg(v_stx_481_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(1u);
v_optType_485_ = l_Lean_Syntax_getArg(v_stx_481_, v___x_484_);
v___x_486_ = l_Lean_Syntax_isNone(v_optType_485_);
if (v___x_486_ == 0)
{
lean_object* v_typeSpec_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_typeSpec_487_ = l_Lean_Syntax_getArg(v_optType_485_, v___x_482_);
lean_dec(v_optType_485_);
v___x_488_ = l_Lean_Syntax_getArg(v_typeSpec_487_, v___x_484_);
lean_dec(v_typeSpec_487_);
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v_binders_483_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_optType_485_);
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_binders_483_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandOptDeclSig___boxed(lean_object* v_stx_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_Elab_expandOptDeclSig(v_stx_493_);
lean_dec(v_stx_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig(lean_object* v_stx_495_){
_start:
{
lean_object* v___x_496_; lean_object* v_binders_497_; lean_object* v___x_498_; lean_object* v_typeSpec_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v_binders_497_ = l_Lean_Syntax_getArg(v_stx_495_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(1u);
v_typeSpec_499_ = l_Lean_Syntax_getArg(v_stx_495_, v___x_498_);
v___x_500_ = l_Lean_Syntax_getArg(v_typeSpec_499_, v___x_498_);
lean_dec(v_typeSpec_499_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_binders_497_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_expandDeclSig___boxed(lean_object* v_stx_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Elab_expandDeclSig(v_stx_502_);
lean_dec(v_stx_502_);
return v_res_503_;
}
}
uint8_t l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(lean_object* v_a_504_, lean_object* v_x_505_){
_start:
{
if (lean_obj_tag(v_x_505_) == 0)
{
uint8_t v___x_506_; 
v___x_506_ = 0;
return v___x_506_;
}
else
{
lean_object* v_head_507_; lean_object* v_tail_508_; uint8_t v___x_509_; 
v_head_507_ = lean_ctor_get(v_x_505_, 0);
v_tail_508_ = lean_ctor_get(v_x_505_, 1);
v___x_509_ = lean_name_eq(v_a_504_, v_head_507_);
if (v___x_509_ == 0)
{
v_x_505_ = v_tail_508_;
goto _start;
}
else
{
return v___x_509_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_504_ = stack[0].m_obj;
lean_object* v_x_505_ = stack[1].m_obj;
uint8_t v_res_511_;
v_res_511_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_504_, v_x_505_);
stack->m_num = v_res_511_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(lean_object* v_a_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_512_, v_x_513_);
lean_dec(v_x_513_);
lean_dec(v_a_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(lean_object* v_allUserParams_516_, lean_object* v_as_517_, size_t v_i_518_, size_t v_stop_519_, lean_object* v_b_520_){
_start:
{
lean_object* v___y_522_; uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_eq(v_i_518_, v_stop_519_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_uget_borrowed(v_as_517_, v_i_518_);
v___x_528_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v___x_527_, v_allUserParams_516_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_inc(v___x_527_);
v___x_529_ = lean_array_push(v_b_520_, v___x_527_);
v___y_522_ = v___x_529_;
goto v___jp_521_;
}
else
{
v___y_522_ = v_b_520_;
goto v___jp_521_;
}
}
else
{
return v_b_520_;
}
v___jp_521_:
{
size_t v___x_523_; size_t v___x_524_; 
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_add(v_i_518_, v___x_523_);
v_i_518_ = v___x_524_;
v_b_520_ = v___y_522_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_allUserParams_516_ = stack[0].m_obj;
lean_object* v_as_517_ = stack[1].m_obj;
size_t v_i_518_ = stack[2].m_num;
size_t v_stop_519_ = stack[3].m_num;
lean_object* v_b_520_ = stack[4].m_obj;
lean_object* v_res_530_;
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_516_, v_as_517_, v_i_518_, v_stop_519_, v_b_520_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(lean_object* v_allUserParams_531_, lean_object* v_as_532_, lean_object* v_i_533_, lean_object* v_stop_534_, lean_object* v_b_535_){
_start:
{
size_t v_i_boxed_536_; size_t v_stop_boxed_537_; lean_object* v_res_538_; 
v_i_boxed_536_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_stop_boxed_537_ = lean_unbox_usize(v_stop_534_);
lean_dec(v_stop_534_);
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_531_, v_as_532_, v_i_boxed_536_, v_stop_boxed_537_, v_b_535_);
lean_dec_ref(v_as_532_);
lean_dec(v_allUserParams_531_);
return v_res_538_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(lean_object* v_a_539_, lean_object* v_as_540_, size_t v_i_541_, size_t v_stop_542_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_541_, v_stop_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = lean_array_uget_borrowed(v_as_540_, v_i_541_);
v___x_545_ = lean_name_eq(v_a_539_, v___x_544_);
if (v___x_545_ == 0)
{
size_t v___x_546_; size_t v___x_547_; 
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_541_, v___x_546_);
v_i_541_ = v___x_547_;
goto _start;
}
else
{
return v___x_545_;
}
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_539_ = stack[0].m_obj;
lean_object* v_as_540_ = stack[1].m_obj;
size_t v_i_541_ = stack[2].m_num;
size_t v_stop_542_ = stack[3].m_num;
uint8_t v_res_550_;
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_539_, v_as_540_, v_i_541_, v_stop_542_);
stack->m_num = v_res_550_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(lean_object* v_a_551_, lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; uint8_t v_res_557_; lean_object* v_r_558_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_551_, v_as_552_, v_i_boxed_555_, v_stop_boxed_556_);
lean_dec_ref(v_as_552_);
lean_dec(v_a_551_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
uint8_t l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(lean_object* v_as_559_, lean_object* v_a_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_array_get_size(v_as_559_);
v___x_563_ = lean_nat_dec_lt(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
return v___x_563_;
}
else
{
if (v___x_563_ == 0)
{
return v___x_563_;
}
else
{
size_t v___x_564_; size_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_560_, v_as_559_, v___x_564_, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_559_ = stack[0].m_obj;
lean_object* v_a_560_ = stack[1].m_obj;
uint8_t v_res_567_;
v_res_567_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_559_, v_a_560_);
stack->m_num = v_res_567_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(lean_object* v_as_568_, lean_object* v_a_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_as_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(lean_object* v_usedParams_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
return v_x_573_;
}
else
{
lean_object* v_head_575_; lean_object* v_tail_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_head_575_ = lean_ctor_get(v_x_574_, 0);
v_tail_576_ = lean_ctor_get(v_x_574_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_574_);
if (v_isSharedCheck_586_ == 0)
{
v___x_578_ = v_x_574_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_tail_576_);
lean_inc(v_head_575_);
lean_dec(v_x_574_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint8_t v___x_580_; 
v___x_580_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_572_, v_head_575_);
if (v___x_580_ == 0)
{
lean_del_object(v___x_578_);
lean_dec(v_head_575_);
v_x_574_ = v_tail_576_;
goto _start;
}
else
{
lean_object* v___x_583_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_x_573_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_head_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_x_573_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
v_x_573_ = v___x_583_;
v_x_574_ = v_tail_576_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(lean_object* v_usedParams_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_587_, v_x_588_, v_x_589_);
lean_dec_ref(v_usedParams_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(lean_object* v_usedParams_591_, lean_object* v_scopeParams_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_box(0);
return v___x_594_;
}
else
{
lean_object* v_head_595_; lean_object* v_tail_596_; uint8_t v___x_597_; 
v_head_595_ = lean_ctor_get(v_x_593_, 0);
v_tail_596_ = lean_ctor_get(v_x_593_, 1);
v___x_597_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_usedParams_591_, v_head_595_);
if (v___x_597_ == 0)
{
uint8_t v___x_598_; 
v___x_598_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_head_595_, v_scopeParams_592_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_inc(v_head_595_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_head_595_);
return v___x_599_;
}
else
{
if (v___x_597_ == 0)
{
v_x_593_ = v_tail_596_;
goto _start;
}
else
{
lean_object* v___x_601_; 
lean_inc(v_head_595_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_head_595_);
return v___x_601_;
}
}
}
else
{
v_x_593_ = v_tail_596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(lean_object* v_usedParams_603_, lean_object* v_scopeParams_604_, lean_object* v_x_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_603_, v_scopeParams_604_, v_x_605_);
lean_dec(v_x_605_);
lean_dec(v_scopeParams_604_);
lean_dec_ref(v_usedParams_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(lean_object* v_hi_607_, lean_object* v_pivot_608_, lean_object* v_as_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_lt(v_k_611_, v_hi_607_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_k_611_);
v___x_613_ = lean_array_fswap(v_as_609_, v_i_610_, v_hi_607_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v_i_610_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_array_fget_borrowed(v_as_609_, v_k_611_);
v___x_616_ = l_Lean_Name_lt(v___x_615_, v_pivot_608_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_k_611_, v___x_617_);
lean_dec(v_k_611_);
v_k_611_ = v___x_618_;
goto _start;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_620_ = lean_array_fswap(v_as_609_, v_i_610_, v_k_611_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_i_610_, v___x_621_);
lean_dec(v_i_610_);
v___x_623_ = lean_nat_add(v_k_611_, v___x_621_);
lean_dec(v_k_611_);
v_as_609_ = v___x_620_;
v_i_610_ = v___x_622_;
v_k_611_ = v___x_623_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(lean_object* v_hi_625_, lean_object* v_pivot_626_, lean_object* v_as_627_, lean_object* v_i_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_625_, v_pivot_626_, v_as_627_, v_i_628_, v_k_629_);
lean_dec(v_pivot_626_);
lean_dec(v_hi_625_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(lean_object* v_n_631_, lean_object* v_as_632_, lean_object* v_lo_633_, lean_object* v_hi_634_){
_start:
{
lean_object* v___y_636_; uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_lt(v_lo_633_, v_hi_634_);
if (v___x_646_ == 0)
{
lean_dec(v_lo_633_);
return v_as_632_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_mid_649_; lean_object* v___y_651_; lean_object* v___y_657_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_647_ = lean_nat_add(v_lo_633_, v_hi_634_);
v___x_648_ = lean_unsigned_to_nat(1u);
v_mid_649_ = lean_nat_shiftr(v___x_647_, v___x_648_);
lean_dec(v___x_647_);
v___x_662_ = lean_array_fget_borrowed(v_as_632_, v_mid_649_);
v___x_663_ = lean_array_fget_borrowed(v_as_632_, v_lo_633_);
v___x_664_ = l_Lean_Name_lt(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
v___y_657_ = v_as_632_;
goto v___jp_656_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = lean_array_fswap(v_as_632_, v_lo_633_, v_mid_649_);
v___y_657_ = v___x_665_;
goto v___jp_656_;
}
v___jp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = lean_array_fget_borrowed(v___y_651_, v_mid_649_);
v___x_653_ = lean_array_fget_borrowed(v___y_651_, v_hi_634_);
v___x_654_ = l_Lean_Name_lt(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v_mid_649_);
v___y_636_ = v___y_651_;
goto v___jp_635_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = lean_array_fswap(v___y_651_, v_mid_649_, v_hi_634_);
lean_dec(v_mid_649_);
v___y_636_ = v___x_655_;
goto v___jp_635_;
}
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_fget_borrowed(v___y_657_, v_hi_634_);
v___x_659_ = lean_array_fget_borrowed(v___y_657_, v_lo_633_);
v___x_660_ = l_Lean_Name_lt(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
v___y_651_ = v___y_657_;
goto v___jp_650_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_array_fswap(v___y_657_, v_lo_633_, v_hi_634_);
v___y_651_ = v___x_661_;
goto v___jp_650_;
}
}
}
v___jp_635_:
{
lean_object* v_pivot_637_; lean_object* v___x_638_; lean_object* v_fst_639_; lean_object* v_snd_640_; uint8_t v___x_641_; 
v_pivot_637_ = lean_array_fget(v___y_636_, v_hi_634_);
lean_inc_n(v_lo_633_, 2);
v___x_638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_634_, v_pivot_637_, v___y_636_, v_lo_633_, v_lo_633_);
lean_dec(v_pivot_637_);
v_fst_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_fst_639_);
v_snd_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_snd_640_);
lean_dec_ref(v___x_638_);
v___x_641_ = lean_nat_dec_le(v_hi_634_, v_fst_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_631_, v_snd_640_, v_lo_633_, v_fst_639_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_fst_639_, v___x_643_);
lean_dec(v_fst_639_);
v_as_632_ = v___x_642_;
v_lo_633_ = v___x_644_;
goto _start;
}
else
{
lean_dec(v_fst_639_);
lean_dec(v_lo_633_);
return v_snd_640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(lean_object* v_n_666_, lean_object* v_as_667_, lean_object* v_lo_668_, lean_object* v_hi_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_666_, v_as_667_, v_lo_668_, v_hi_669_);
lean_dec(v_hi_669_);
lean_dec(v_n_666_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object* v_scopeParams_675_, lean_object* v_allUserParams_676_, lean_object* v_usedParams_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(v_usedParams_677_, v_scopeParams_675_, v_allUserParams_676_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v___x_679_; lean_object* v_result_680_; lean_object* v___y_682_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___x_698_; lean_object* v___y_700_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_679_ = lean_box(0);
lean_inc(v_allUserParams_676_);
v_result_680_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(v_usedParams_677_, v___x_679_, v_allUserParams_676_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_array_get_size(v_usedParams_677_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__0));
v___x_708_ = lean_nat_dec_lt(v___x_698_, v___x_706_);
if (v___x_708_ == 0)
{
lean_dec(v_allUserParams_676_);
v___y_700_ = v___x_707_;
goto v___jp_699_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_le(v___x_706_, v___x_706_);
if (v___x_709_ == 0)
{
if (v___x_708_ == 0)
{
lean_dec(v_allUserParams_676_);
v___y_700_ = v___x_707_;
goto v___jp_699_;
}
else
{
size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_706_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_676_, v_usedParams_677_, v___x_710_, v___x_711_, v___x_707_);
lean_dec(v_allUserParams_676_);
v___y_700_ = v___x_712_;
goto v___jp_699_;
}
}
else
{
size_t v___x_713_; size_t v___x_714_; lean_object* v___x_715_; 
v___x_713_ = ((size_t)0ULL);
v___x_714_ = lean_usize_of_nat(v___x_706_);
v___x_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_676_, v_usedParams_677_, v___x_713_, v___x_714_, v___x_707_);
lean_dec(v_allUserParams_676_);
v___y_700_ = v___x_715_;
goto v___jp_699_;
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_array_to_list(v___y_682_);
v___x_684_ = l_List_appendTR___redArg(v_result_680_, v___x_683_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
v___jp_686_:
{
lean_object* v___x_691_; 
v___x_691_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec(v___y_687_);
v___y_682_ = v___x_691_;
goto v___jp_681_;
}
v___jp_692_:
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_le(v___y_696_, v___y_695_);
if (v___x_697_ == 0)
{
lean_dec(v___y_695_);
lean_inc(v___y_696_);
v___y_687_ = v___y_693_;
v___y_688_ = v___y_694_;
v___y_689_ = v___y_696_;
v___y_690_ = v___y_696_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___y_693_;
v___y_688_ = v___y_694_;
v___y_689_ = v___y_696_;
v___y_690_ = v___y_695_;
goto v___jp_686_;
}
}
v___jp_699_:
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = lean_array_get_size(v___y_700_);
v___x_702_ = lean_nat_dec_eq(v___x_701_, v___x_698_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(1u);
v___x_704_ = lean_nat_sub(v___x_701_, v___x_703_);
v___x_705_ = lean_nat_dec_le(v___x_698_, v___x_704_);
if (v___x_705_ == 0)
{
lean_inc(v___x_704_);
v___y_693_ = v___x_701_;
v___y_694_ = v___y_700_;
v___y_695_ = v___x_704_;
v___y_696_ = v___x_704_;
goto v___jp_692_;
}
else
{
v___y_693_ = v___x_701_;
v___y_694_ = v___y_700_;
v___y_695_ = v___x_704_;
v___y_696_ = v___x_698_;
goto v___jp_692_;
}
}
else
{
v___y_682_ = v___y_700_;
goto v___jp_681_;
}
}
}
else
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_allUserParams_676_);
v_val_716_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_729_ == 0)
{
v___x_718_ = v___x_678_;
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v___x_678_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_729_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__1));
v___x_721_ = 1;
v___x_722_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_716_, v___x_721_);
v___x_723_ = lean_string_append(v___x_720_, v___x_722_);
lean_dec_ref(v___x_722_);
v___x_724_ = ((lean_object*)(l_Lean_Elab_sortDeclLevelParams___closed__2));
v___x_725_ = lean_string_append(v___x_723_, v___x_724_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 0);
lean_ctor_set(v___x_718_, 0, v___x_725_);
v___x_727_ = v___x_718_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_sortDeclLevelParams___boxed(lean_object* v_scopeParams_730_, lean_object* v_allUserParams_731_, lean_object* v_usedParams_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Elab_sortDeclLevelParams(v_scopeParams_730_, v_allUserParams_731_, v_usedParams_732_);
lean_dec_ref(v_usedParams_732_);
lean_dec(v_scopeParams_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(lean_object* v_n_734_, lean_object* v_as_735_, lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_w_738_, lean_object* v_hlo_739_, lean_object* v_hhi_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_734_, v_as_735_, v_lo_736_, v_hi_737_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(lean_object* v_n_742_, lean_object* v_as_743_, lean_object* v_lo_744_, lean_object* v_hi_745_, lean_object* v_w_746_, lean_object* v_hlo_747_, lean_object* v_hhi_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_742_, v_as_743_, v_lo_744_, v_hi_745_, v_w_746_, v_hlo_747_, v_hhi_748_);
lean_dec(v_hi_745_);
lean_dec(v_n_742_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(lean_object* v_n_750_, lean_object* v_lo_751_, lean_object* v_hi_752_, lean_object* v_hhi_753_, lean_object* v_pivot_754_, lean_object* v_as_755_, lean_object* v_i_756_, lean_object* v_k_757_, lean_object* v_ilo_758_, lean_object* v_ik_759_, lean_object* v_w_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_752_, v_pivot_754_, v_as_755_, v_i_756_, v_k_757_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(lean_object* v_n_762_, lean_object* v_lo_763_, lean_object* v_hi_764_, lean_object* v_hhi_765_, lean_object* v_pivot_766_, lean_object* v_as_767_, lean_object* v_i_768_, lean_object* v_k_769_, lean_object* v_ilo_770_, lean_object* v_ik_771_, lean_object* v_w_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_762_, v_lo_763_, v_hi_764_, v_hhi_765_, v_pivot_766_, v_as_767_, v_i_768_, v_k_769_, v_ilo_770_, v_ik_771_, v_w_772_);
lean_dec(v_pivot_766_);
lean_dec(v_hi_764_);
lean_dec(v_lo_763_);
lean_dec(v_n_762_);
return v_res_773_;
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
