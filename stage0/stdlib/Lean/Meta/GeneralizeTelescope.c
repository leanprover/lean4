// Lean compiler output
// Module: Lean.Meta.GeneralizeTelescope
// Imports: public import Lean.Meta.KAbstract public import Lean.Meta.Check
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to create telescope generalizing "};
static const lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_generalizeTelescope___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_generalizeTelescope___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_generalizeTelescope___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes(lean_object* v_e_1_, lean_object* v_eNew_2_, lean_object* v_entries_3_, lean_object* v_i_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = lean_array_get_size(v_entries_3_);
v___x_11_ = lean_nat_dec_lt(v_i_4_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; 
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_i_4_);
lean_dec_ref(v_e_1_);
v___x_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_12_, 0, v_entries_3_);
return v___x_12_;
}
else
{
lean_object* v_entry_13_; lean_object* v_expr_14_; lean_object* v_type_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_42_; 
v_entry_13_ = lean_array_fget(v_entries_3_, v_i_4_);
v_expr_14_ = lean_ctor_get(v_entry_13_, 0);
v_type_15_ = lean_ctor_get(v_entry_13_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_entry_13_);
if (v_isSharedCheck_42_ == 0)
{
v___x_17_ = v_entry_13_;
v_isShared_18_ = v_isSharedCheck_42_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_type_15_);
lean_inc(v_expr_14_);
lean_dec(v_entry_13_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_42_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_box(0);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc_ref(v_e_1_);
v___x_20_ = l_Lean_Meta_kabstract(v_type_15_, v_e_1_, v___x_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; uint8_t v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref(v___x_20_);
v___x_22_ = l_Lean_Expr_hasLooseBVars(v_a_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_a_21_);
lean_del_object(v___x_17_);
lean_dec_ref(v_expr_14_);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = lean_nat_add(v_i_4_, v___x_23_);
lean_dec(v_i_4_);
v_i_4_ = v___x_24_;
goto _start;
}
else
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_expr_instantiate1(v_a_21_, v_eNew_2_);
lean_dec(v_a_21_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___x_26_);
v___x_28_ = v___x_17_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_expr_14_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_26_);
v___x_28_ = v_reuseFailAlloc_33_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*2, v___x_22_);
v___x_29_ = lean_array_fset(v_entries_3_, v_i_4_, v___x_28_);
v___x_30_ = lean_unsigned_to_nat(1u);
v___x_31_ = lean_nat_add(v_i_4_, v___x_30_);
lean_dec(v_i_4_);
v_entries_3_ = v___x_29_;
v_i_4_ = v___x_31_;
goto _start;
}
}
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_del_object(v___x_17_);
lean_dec_ref(v_expr_14_);
lean_dec(v_a_8_);
lean_dec_ref(v_a_7_);
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_i_4_);
lean_dec_ref(v_entries_3_);
lean_dec_ref(v_e_1_);
v_a_34_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_20_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_20_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(lean_object* v_e_43_, lean_object* v_eNew_44_, lean_object* v_entries_45_, lean_object* v_i_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_43_, v_eNew_44_, v_entries_45_, v_i_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec_ref(v_eNew_44_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(lean_object* v_msgData_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_mctx_62_; lean_object* v_lctx_63_; lean_object* v_options_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_env_60_);
lean_dec(v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_55_);
v_mctx_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_mctx_62_);
lean_dec(v___x_61_);
v_lctx_63_ = lean_ctor_get(v___y_54_, 2);
v_options_64_ = lean_ctor_get(v___y_56_, 2);
lean_inc_ref(v_options_64_);
lean_inc_ref(v_lctx_63_);
v___x_65_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_65_, 0, v_env_60_);
lean_ctor_set(v___x_65_, 1, v_mctx_62_);
lean_ctor_set(v___x_65_, 2, v_lctx_63_);
lean_ctor_set(v___x_65_, 3, v_options_64_);
v___x_66_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_msgData_53_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(lean_object* v_msgData_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msgData_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(lean_object* v_msg_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_ref_81_; lean_object* v___x_82_; lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_ref_81_ = lean_ctor_get(v___y_78_, 5);
v___x_82_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msg_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
lean_inc(v_ref_81_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_ref_81_);
lean_ctor_set(v___x_87_, 1, v_a_83_);
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 1);
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(lean_object* v_msg_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(lean_object* v_k_99_, lean_object* v_b_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_apply_6(v_k_99_, v_b_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, lean_box(0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_107_, lean_object* v_b_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(v_k_107_, v_b_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(lean_object* v_name_115_, uint8_t v_bi_116_, lean_object* v_type_117_, lean_object* v_k_118_, uint8_t v_kind_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; 
v___f_125_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_125_, 0, v_k_118_);
v___x_126_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_115_, v_bi_116_, v_type_117_, v___f_125_, v_kind_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
else
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_a_135_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_126_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_126_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(lean_object* v_name_143_, lean_object* v_bi_144_, lean_object* v_type_145_, lean_object* v_k_146_, lean_object* v_kind_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
uint8_t v_bi_boxed_153_; uint8_t v_kind_boxed_154_; lean_object* v_res_155_; 
v_bi_boxed_153_ = lean_unbox(v_bi_144_);
v_kind_boxed_154_ = lean_unbox(v_kind_147_);
v_res_155_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_143_, v_bi_boxed_153_, v_type_145_, v_k_146_, v_kind_boxed_154_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(lean_object* v_name_156_, lean_object* v_type_157_, lean_object* v_k_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
uint8_t v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; 
v___x_164_ = 0;
v___x_165_ = 0;
v___x_166_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_156_, v___x_164_, v_type_157_, v_k_158_, v___x_165_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(lean_object* v_name_167_, lean_object* v_type_168_, lean_object* v_k_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_167_, v_type_168_, v_k_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
if (lean_obj_tag(v_a_176_) == 0)
{
lean_object* v___x_178_; 
v___x_178_ = l_List_reverse___redArg(v_a_177_);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_189_; 
v_head_179_ = lean_ctor_get(v_a_176_, 0);
v_tail_180_ = lean_ctor_get(v_a_176_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v_a_176_);
if (v_isSharedCheck_189_ == 0)
{
v___x_182_ = v_a_176_;
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_head_179_);
lean_dec(v_a_176_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_184_ = l_Lean_MessageData_ofExpr(v_head_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_a_177_);
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_a_177_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
v_a_176_ = v_tail_180_;
v_a_177_ = v___x_186_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(size_t v_sz_190_, size_t v_i_191_, lean_object* v_bs_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_lt(v_i_191_, v_sz_190_);
if (v___x_193_ == 0)
{
return v_bs_192_;
}
else
{
lean_object* v_v_194_; lean_object* v_expr_195_; lean_object* v___x_196_; lean_object* v_bs_x27_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v_v_194_ = lean_array_uget_borrowed(v_bs_192_, v_i_191_);
v_expr_195_ = lean_ctor_get(v_v_194_, 0);
lean_inc_ref(v_expr_195_);
v___x_196_ = lean_unsigned_to_nat(0u);
v_bs_x27_197_ = lean_array_uset(v_bs_192_, v_i_191_, v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_191_, v___x_198_);
v___x_200_ = lean_array_uset(v_bs_x27_197_, v_i_191_, v_expr_195_);
v_i_191_ = v___x_199_;
v_bs_192_ = v___x_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(lean_object* v_sz_202_, lean_object* v_i_203_, lean_object* v_bs_204_){
_start:
{
size_t v_sz_boxed_205_; size_t v_i_boxed_206_; lean_object* v_res_207_; 
v_sz_boxed_205_ = lean_unbox_usize(v_sz_202_);
lean_dec(v_sz_202_);
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_boxed_205_, v_i_boxed_206_, v_bs_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(lean_object* v_i_208_, lean_object* v_e_209_, lean_object* v_entries_210_, lean_object* v_fvars_211_, lean_object* v_k_212_, lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(v_i_208_, v_e_209_, v_entries_210_, v_fvars_211_, v_k_212_, v_x_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v_i_208_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(lean_object* v_k_226_, lean_object* v_entries_227_, lean_object* v_i_228_, lean_object* v_fvars_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_baseUserName_236_; lean_object* v_e_237_; lean_object* v_type_238_; lean_object* v___y_239_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_256_; lean_object* v___y_257_; lean_object* v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = lean_array_get_size(v_entries_227_);
v___x_264_ = lean_nat_dec_lt(v_i_228_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_i_228_);
lean_dec_ref(v_entries_227_);
v___x_265_ = lean_apply_6(v_k_226_, v_fvars_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, lean_box(0));
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v_expr_267_; lean_object* v_type_268_; uint8_t v_modified_269_; lean_object* v___y_271_; lean_object* v___y_272_; lean_object* v___y_273_; lean_object* v___y_274_; 
v___x_266_ = lean_array_fget_borrowed(v_entries_227_, v_i_228_);
v_expr_267_ = lean_ctor_get(v___x_266_, 0);
v_type_268_ = lean_ctor_get(v___x_266_, 1);
v_modified_269_ = lean_ctor_get_uint8(v___x_266_, sizeof(void*)*2);
if (lean_obj_tag(v_expr_267_) == 1)
{
if (v_modified_269_ == 0)
{
lean_object* v_fvarId_304_; lean_object* v___x_305_; 
v_fvarId_304_ = lean_ctor_get(v_expr_267_, 0);
lean_inc_ref(v_a_230_);
lean_inc(v_fvarId_304_);
v___x_305_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_304_, v_a_230_, v_a_232_, v_a_233_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref(v___x_305_);
if (lean_obj_tag(v_a_306_) == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref(v_a_306_);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_228_, v___x_307_);
lean_dec(v_i_228_);
lean_inc_ref(v_expr_267_);
v___x_309_ = lean_array_push(v_fvars_229_, v_expr_267_);
v_i_228_ = v___x_308_;
v_fvars_229_ = v___x_309_;
goto _start;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_LocalDecl_userName(v_a_306_);
lean_dec_ref(v_a_306_);
lean_inc_ref(v_type_268_);
lean_inc_ref(v_expr_267_);
v_baseUserName_236_ = v___x_311_;
v_e_237_ = v_expr_267_;
v_type_238_ = v_type_268_;
v___y_239_ = v_a_230_;
v___y_240_ = v_a_231_;
v___y_241_ = v_a_232_;
v___y_242_ = v_a_233_;
goto v___jp_235_;
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec_ref(v_fvars_229_);
lean_dec(v_i_228_);
lean_dec_ref(v_entries_227_);
lean_dec_ref(v_k_226_);
v_a_312_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_305_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_305_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
v___y_271_ = v_a_230_;
v___y_272_ = v_a_231_;
v___y_273_ = v_a_232_;
v___y_274_ = v_a_233_;
goto v___jp_270_;
}
}
else
{
v___y_271_ = v_a_230_;
v___y_272_ = v_a_231_;
v___y_273_ = v_a_232_;
v___y_274_ = v_a_233_;
goto v___jp_270_;
}
v___jp_270_:
{
if (v_modified_269_ == 0)
{
lean_inc_ref(v_type_268_);
lean_inc_ref(v_expr_267_);
v___y_256_ = v_expr_267_;
v___y_257_ = v_type_268_;
v___y_258_ = v___y_271_;
v___y_259_ = v___y_272_;
v___y_260_ = v___y_273_;
v___y_261_ = v___y_274_;
goto v___jp_255_;
}
else
{
lean_object* v___x_275_; 
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc_ref(v_type_268_);
v___x_275_ = l_Lean_Meta_isTypeCorrect(v_type_268_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; uint8_t v___x_277_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref(v___x_275_);
v___x_277_ = lean_unbox(v_a_276_);
lean_dec(v_a_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; size_t v_sz_279_; size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_278_ = lean_obj_once(&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3, &l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once, _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3);
v_sz_279_ = lean_array_size(v_entries_227_);
v___x_280_ = ((size_t)0ULL);
lean_inc_ref(v_entries_227_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_279_, v___x_280_, v_entries_227_);
v___x_282_ = lean_array_to_list(v___x_281_);
v___x_283_ = lean_box(0);
v___x_284_ = l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(v___x_282_, v___x_283_);
v___x_285_ = l_Lean_MessageData_ofList(v___x_284_);
v___x_286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_278_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v___x_286_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_dec_ref(v___x_287_);
lean_inc_ref(v_type_268_);
lean_inc_ref(v_expr_267_);
v___y_256_ = v_expr_267_;
v___y_257_ = v_type_268_;
v___y_258_ = v___y_271_;
v___y_259_ = v___y_272_;
v___y_260_ = v___y_273_;
v___y_261_ = v___y_274_;
goto v___jp_255_;
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v_fvars_229_);
lean_dec(v_i_228_);
lean_dec_ref(v_entries_227_);
lean_dec_ref(v_k_226_);
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
else
{
lean_inc_ref(v_type_268_);
lean_inc_ref(v_expr_267_);
v___y_256_ = v_expr_267_;
v___y_257_ = v_type_268_;
v___y_258_ = v___y_271_;
v___y_259_ = v___y_272_;
v___y_260_ = v___y_273_;
v___y_261_ = v___y_274_;
goto v___jp_255_;
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec_ref(v_fvars_229_);
lean_dec(v_i_228_);
lean_dec_ref(v_entries_227_);
lean_dec_ref(v_k_226_);
v_a_296_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_275_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_275_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
v___jp_235_:
{
lean_object* v___x_243_; 
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
v___x_243_ = l_Lean_Core_mkFreshUserName(v_baseUserName_236_, v___y_241_, v___y_242_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___f_245_; lean_object* v___x_246_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref(v___x_243_);
v___f_245_ = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_245_, 0, v_i_228_);
lean_closure_set(v___f_245_, 1, v_e_237_);
lean_closure_set(v___f_245_, 2, v_entries_227_);
lean_closure_set(v___f_245_, 3, v_fvars_229_);
lean_closure_set(v___f_245_, 4, v_k_226_);
v___x_246_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_a_244_, v_type_238_, v___f_245_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec_ref(v_type_238_);
lean_dec_ref(v_e_237_);
lean_dec_ref(v_fvars_229_);
lean_dec(v_i_228_);
lean_dec_ref(v_entries_227_);
lean_dec_ref(v_k_226_);
v_a_247_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_243_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_243_);
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
lean_object* v___x_262_; 
v___x_262_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1));
v_baseUserName_236_ = v___x_262_;
v_e_237_ = v___y_256_;
v_type_238_ = v___y_257_;
v___y_239_ = v___y_258_;
v___y_240_ = v___y_259_;
v___y_241_ = v___y_260_;
v___y_242_ = v___y_261_;
goto v___jp_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(lean_object* v_i_320_, lean_object* v_e_321_, lean_object* v_entries_322_, lean_object* v_fvars_323_, lean_object* v_k_324_, lean_object* v_x_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_i_320_, v___x_331_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___x_332_);
v___x_333_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_321_, v_x_325_, v_entries_322_, v___x_332_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
v___x_335_ = lean_array_push(v_fvars_323_, v_x_325_);
v___x_336_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_324_, v_a_334_, v___x_332_, v___x_335_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_336_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v___x_332_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec_ref(v_x_325_);
lean_dec_ref(v_k_324_);
lean_dec_ref(v_fvars_323_);
v_a_337_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_333_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(lean_object* v_k_345_, lean_object* v_entries_346_, lean_object* v_i_347_, lean_object* v_fvars_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_345_, v_entries_346_, v_i_347_, v_fvars_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object* v_00_u03b1_355_, lean_object* v_k_356_, lean_object* v_entries_357_, lean_object* v_i_358_, lean_object* v_fvars_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_356_, v_entries_357_, v_i_358_, v_fvars_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(lean_object* v_00_u03b1_366_, lean_object* v_k_367_, lean_object* v_entries_368_, lean_object* v_i_369_, lean_object* v_fvars_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(v_00_u03b1_366_, v_k_367_, v_entries_368_, v_i_369_, v_fvars_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_object* v_00_u03b1_377_, lean_object* v_name_378_, uint8_t v_bi_379_, lean_object* v_type_380_, lean_object* v_k_381_, uint8_t v_kind_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_378_, v_bi_379_, v_type_380_, v_k_381_, v_kind_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(lean_object* v_00_u03b1_389_, lean_object* v_name_390_, lean_object* v_bi_391_, lean_object* v_type_392_, lean_object* v_k_393_, lean_object* v_kind_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v_bi_boxed_400_; uint8_t v_kind_boxed_401_; lean_object* v_res_402_; 
v_bi_boxed_400_ = lean_unbox(v_bi_391_);
v_kind_boxed_401_ = lean_unbox(v_kind_394_);
v_res_402_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(v_00_u03b1_389_, v_name_390_, v_bi_boxed_400_, v_type_392_, v_k_393_, v_kind_boxed_401_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_name_404_, lean_object* v_type_405_, lean_object* v_k_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_404_, v_type_405_, v_k_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_name_414_, lean_object* v_type_415_, lean_object* v_k_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(v_00_u03b1_413_, v_name_414_, v_type_415_, v_k_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(lean_object* v_00_u03b1_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(v_00_u03b1_431_, v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(lean_object* v_e_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_Expr_hasMVar(v_e_439_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_e_439_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v_mctx_445_; lean_object* v___x_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; lean_object* v_cache_450_; lean_object* v_zetaDeltaFVarIds_451_; lean_object* v_postponed_452_; lean_object* v_diag_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v___x_444_ = lean_st_ref_get(v___y_440_);
v_mctx_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_mctx_445_);
lean_dec(v___x_444_);
v___x_446_ = l_Lean_instantiateMVarsCore(v_mctx_445_, v_e_439_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_448_);
lean_dec_ref(v___x_446_);
v___x_449_ = lean_st_ref_take(v___y_440_);
v_cache_450_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_451_ = lean_ctor_get(v___x_449_, 2);
v_postponed_452_ = lean_ctor_get(v___x_449_, 3);
v_diag_453_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_463_);
v___x_455_ = v___x_449_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_diag_453_);
lean_inc(v_postponed_452_);
lean_inc(v_zetaDeltaFVarIds_451_);
lean_inc(v_cache_450_);
lean_dec(v___x_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_snd_448_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_snd_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_cache_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_zetaDeltaFVarIds_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_postponed_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_diag_453_);
v___x_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_st_ref_set(v___y_440_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_fst_447_);
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(lean_object* v_e_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_464_, v___y_465_);
lean_dec(v___y_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_468_, v___y_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(lean_object* v_e_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(v_e_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(size_t v_sz_482_, size_t v_i_483_, lean_object* v_bs_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = lean_usize_dec_lt(v_i_483_, v_sz_482_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; 
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v_bs_484_);
return v___x_491_;
}
else
{
lean_object* v_v_492_; lean_object* v___x_493_; 
v_v_492_ = lean_array_uget(v_bs_484_, v_i_483_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v_v_492_);
v___x_493_ = lean_infer_type(v_v_492_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
v___x_495_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_a_494_, v___y_486_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v_bs_x27_498_; uint8_t v___x_499_; lean_object* v___x_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_unsigned_to_nat(0u);
v_bs_x27_498_ = lean_array_uset(v_bs_484_, v_i_483_, v___x_497_);
v___x_499_ = 0;
v___x_500_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_500_, 0, v_v_492_);
lean_ctor_set(v___x_500_, 1, v_a_496_);
lean_ctor_set_uint8(v___x_500_, sizeof(void*)*2, v___x_499_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_add(v_i_483_, v___x_501_);
v___x_503_ = lean_array_uset(v_bs_x27_498_, v_i_483_, v___x_500_);
v_i_483_ = v___x_502_;
v_bs_484_ = v___x_503_;
goto _start;
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_v_492_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v_bs_484_);
v_a_505_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_495_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_v_492_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec_ref(v_bs_484_);
v_a_513_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_493_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_493_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_530_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_boxed_529_, v_i_boxed_530_, v_bs_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg(lean_object* v_es_534_, lean_object* v_k_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
size_t v_sz_541_; size_t v___x_542_; lean_object* v___x_543_; 
v_sz_541_ = lean_array_size(v_es_534_);
v___x_542_ = ((size_t)0ULL);
lean_inc(v_a_539_);
lean_inc_ref(v_a_538_);
lean_inc(v_a_537_);
lean_inc_ref(v_a_536_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_541_, v___x_542_, v_es_534_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = ((lean_object*)(l_Lean_Meta_generalizeTelescope___redArg___closed__0));
v___x_547_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_535_, v_a_544_, v___x_545_, v___x_546_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
return v___x_547_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec_ref(v_k_535_);
v_a_548_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_543_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_543_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg___boxed(lean_object* v_es_556_, lean_object* v_k_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_556_, v_k_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object* v_00_u03b1_564_, lean_object* v_es_565_, lean_object* v_k_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_565_, v_k_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___boxed(lean_object* v_00_u03b1_573_, lean_object* v_es_574_, lean_object* v_k_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Meta_generalizeTelescope(v_00_u03b1_573_, v_es_574_, v_k_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
return v_res_581_;
}
}
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_KAbstract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_GeneralizeTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_GeneralizeTelescope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_GeneralizeTelescope(builtin);
}
#ifdef __cplusplus
}
#endif
