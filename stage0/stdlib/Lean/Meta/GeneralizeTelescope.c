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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_e_1_);
v___x_20_ = l_Lean_Meta_kabstract(v_type_15_, v_e_1_, v___x_19_, v_a_5_, v_a_6_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; uint8_t v___x_22_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_20_, 1);
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
lean_ctor_set_uint8(v___x_28_, sizeof(void*)*2, v___x_11_);
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
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec_ref(v_eNew_44_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(lean_object* v_msgData_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_env_60_; uint8_t v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; lean_object* v_toCold_64_; lean_object* v_mctx_65_; lean_object* v_lctx_66_; lean_object* v_options_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_59_ = lean_st_ref_get(v___y_57_);
v_env_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_ref(v_env_60_);
lean_dec(v___x_59_);
v___x_61_ = 0;
v_env_62_ = l_Lean_Environment_setRecordingDeps(v_env_60_, v___x_61_);
v___x_63_ = lean_st_ref_get(v___y_55_);
v_toCold_64_ = lean_ctor_get(v___y_56_, 0);
v_mctx_65_ = lean_ctor_get(v___x_63_, 0);
lean_inc_ref(v_mctx_65_);
lean_dec(v___x_63_);
v_lctx_66_ = lean_ctor_get(v___y_54_, 2);
v_options_67_ = lean_ctor_get(v_toCold_64_, 2);
lean_inc_ref(v_options_67_);
lean_inc_ref(v_lctx_66_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v_env_62_);
lean_ctor_set(v___x_68_, 1, v_mctx_65_);
lean_ctor_set(v___x_68_, 2, v_lctx_66_);
lean_ctor_set(v___x_68_, 3, v_options_67_);
v___x_69_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v_msgData_53_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(lean_object* v_msgData_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msgData_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(lean_object* v_msg_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_ref_84_ = lean_ctor_get(v___y_81_, 2);
v___x_85_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msg_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
lean_inc(v_ref_84_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_ref_84_);
lean_ctor_set(v___x_90_, 1, v_a_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 0, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(lean_object* v_k_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
v___x_109_ = lean_apply_6(v_k_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(v_k_110_, v_b_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(lean_object* v_name_118_, uint8_t v_bi_119_, lean_object* v_type_120_, lean_object* v_k_121_, uint8_t v_kind_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_128_, 0, v_k_121_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_118_, v_bi_119_, v_type_120_, v___f_128_, v_kind_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(lean_object* v_name_146_, lean_object* v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, lean_object* v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_bi_boxed_156_; uint8_t v_kind_boxed_157_; lean_object* v_res_158_; 
v_bi_boxed_156_ = lean_unbox(v_bi_147_);
v_kind_boxed_157_ = lean_unbox(v_kind_150_);
v_res_158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_146_, v_bi_boxed_156_, v_type_148_, v_k_149_, v_kind_boxed_157_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(lean_object* v_name_159_, lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = 0;
v___x_168_ = 0;
v___x_169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_159_, v___x_167_, v_type_160_, v_k_161_, v___x_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(lean_object* v_name_170_, lean_object* v_type_171_, lean_object* v_k_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_170_, v_type_171_, v_k_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
if (lean_obj_tag(v_a_179_) == 0)
{
lean_object* v___x_181_; 
v___x_181_ = l_List_reverse___redArg(v_a_180_);
return v___x_181_;
}
else
{
lean_object* v_head_182_; lean_object* v_tail_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_192_; 
v_head_182_ = lean_ctor_get(v_a_179_, 0);
v_tail_183_ = lean_ctor_get(v_a_179_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_192_ == 0)
{
v___x_185_ = v_a_179_;
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_tail_183_);
lean_inc(v_head_182_);
lean_dec(v_a_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = l_Lean_MessageData_ofExpr(v_head_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v_a_180_);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_a_180_);
v___x_189_ = v_reuseFailAlloc_191_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
v_a_179_ = v_tail_183_;
v_a_180_ = v___x_189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(size_t v_sz_193_, size_t v_i_194_, lean_object* v_bs_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_usize_dec_lt(v_i_194_, v_sz_193_);
if (v___x_196_ == 0)
{
return v_bs_195_;
}
else
{
lean_object* v_v_197_; lean_object* v_expr_198_; lean_object* v___x_199_; lean_object* v_bs_x27_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v_v_197_ = lean_array_uget_borrowed(v_bs_195_, v_i_194_);
v_expr_198_ = lean_ctor_get(v_v_197_, 0);
lean_inc_ref(v_expr_198_);
v___x_199_ = lean_unsigned_to_nat(0u);
v_bs_x27_200_ = lean_array_uset(v_bs_195_, v_i_194_, v___x_199_);
v___x_201_ = ((size_t)1ULL);
v___x_202_ = lean_usize_add(v_i_194_, v___x_201_);
v___x_203_ = lean_array_uset(v_bs_x27_200_, v_i_194_, v_expr_198_);
v_i_194_ = v___x_202_;
v_bs_195_ = v___x_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(lean_object* v_sz_205_, lean_object* v_i_206_, lean_object* v_bs_207_){
_start:
{
size_t v_sz_boxed_208_; size_t v_i_boxed_209_; lean_object* v_res_210_; 
v_sz_boxed_208_ = lean_unbox_usize(v_sz_205_);
lean_dec(v_sz_205_);
v_i_boxed_209_ = lean_unbox_usize(v_i_206_);
lean_dec(v_i_206_);
v_res_210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_boxed_208_, v_i_boxed_209_, v_bs_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(lean_object* v_i_211_, lean_object* v_e_212_, lean_object* v_entries_213_, lean_object* v_fvars_214_, lean_object* v_k_215_, lean_object* v_x_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(v_i_211_, v_e_212_, v_entries_213_, v_fvars_214_, v_k_215_, v_x_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v_i_211_);
return v_res_222_;
}
}
static lean_object* _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(lean_object* v_k_229_, lean_object* v_entries_230_, lean_object* v_i_231_, lean_object* v_fvars_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_baseUserName_239_; lean_object* v_e_240_; lean_object* v_type_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; lean_object* v___y_264_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_entries_230_);
v___x_267_ = lean_nat_dec_lt(v_i_231_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec(v_i_231_);
lean_dec_ref(v_entries_230_);
lean_inc(v_a_236_);
lean_inc_ref(v_a_235_);
lean_inc(v_a_234_);
lean_inc_ref(v_a_233_);
v___x_268_ = lean_apply_6(v_k_229_, v_fvars_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, lean_box(0));
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v_expr_270_; lean_object* v_type_271_; uint8_t v_modified_272_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; 
v___x_269_ = lean_array_fget_borrowed(v_entries_230_, v_i_231_);
v_expr_270_ = lean_ctor_get(v___x_269_, 0);
v_type_271_ = lean_ctor_get(v___x_269_, 1);
v_modified_272_ = lean_ctor_get_uint8(v___x_269_, sizeof(void*)*2);
if (lean_obj_tag(v_expr_270_) == 1)
{
if (v_modified_272_ == 0)
{
lean_object* v_fvarId_307_; lean_object* v___x_308_; 
v_fvarId_307_ = lean_ctor_get(v_expr_270_, 0);
lean_inc(v_fvarId_307_);
v___x_308_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_307_, v_a_233_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
if (lean_obj_tag(v_a_309_) == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec_ref_known(v_a_309_, 4);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lean_nat_add(v_i_231_, v___x_310_);
lean_dec(v_i_231_);
lean_inc_ref(v_expr_270_);
v___x_312_ = lean_array_push(v_fvars_232_, v_expr_270_);
v_i_231_ = v___x_311_;
v_fvars_232_ = v___x_312_;
goto _start;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_LocalDecl_userName(v_a_309_);
lean_dec_ref_known(v_a_309_, 5);
lean_inc_ref(v_type_271_);
lean_inc_ref(v_expr_270_);
v_baseUserName_239_ = v___x_314_;
v_e_240_ = v_expr_270_;
v_type_241_ = v_type_271_;
v___y_242_ = v_a_233_;
v___y_243_ = v_a_234_;
v___y_244_ = v_a_235_;
v___y_245_ = v_a_236_;
goto v___jp_238_;
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_fvars_232_);
lean_dec(v_i_231_);
lean_dec_ref(v_entries_230_);
lean_dec_ref(v_k_229_);
v_a_315_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_308_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_308_);
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
else
{
v___y_274_ = v_a_233_;
v___y_275_ = v_a_234_;
v___y_276_ = v_a_235_;
v___y_277_ = v_a_236_;
goto v___jp_273_;
}
}
else
{
v___y_274_ = v_a_233_;
v___y_275_ = v_a_234_;
v___y_276_ = v_a_235_;
v___y_277_ = v_a_236_;
goto v___jp_273_;
}
v___jp_273_:
{
if (v_modified_272_ == 0)
{
lean_inc_ref(v_expr_270_);
lean_inc_ref(v_type_271_);
v___y_259_ = v_type_271_;
v___y_260_ = v_expr_270_;
v___y_261_ = v___y_274_;
v___y_262_ = v___y_275_;
v___y_263_ = v___y_276_;
v___y_264_ = v___y_277_;
goto v___jp_258_;
}
else
{
lean_object* v___x_278_; 
lean_inc_ref(v_type_271_);
v___x_278_ = l_Lean_Meta_isTypeCorrect(v_type_271_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; uint8_t v___x_280_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = lean_unbox(v_a_279_);
lean_dec(v_a_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; size_t v_sz_282_; size_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_281_ = lean_obj_once(&l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3, &l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once, _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3);
v_sz_282_ = lean_array_size(v_entries_230_);
v___x_283_ = ((size_t)0ULL);
lean_inc_ref(v_entries_230_);
v___x_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_282_, v___x_283_, v_entries_230_);
v___x_285_ = lean_array_to_list(v___x_284_);
v___x_286_ = lean_box(0);
v___x_287_ = l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(v___x_285_, v___x_286_);
v___x_288_ = l_Lean_MessageData_ofList(v___x_287_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_281_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v___x_289_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_dec_ref_known(v___x_290_, 1);
lean_inc_ref(v_expr_270_);
lean_inc_ref(v_type_271_);
v___y_259_ = v_type_271_;
v___y_260_ = v_expr_270_;
v___y_261_ = v___y_274_;
v___y_262_ = v___y_275_;
v___y_263_ = v___y_276_;
v___y_264_ = v___y_277_;
goto v___jp_258_;
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_fvars_232_);
lean_dec(v_i_231_);
lean_dec_ref(v_entries_230_);
lean_dec_ref(v_k_229_);
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_inc_ref(v_expr_270_);
lean_inc_ref(v_type_271_);
v___y_259_ = v_type_271_;
v___y_260_ = v_expr_270_;
v___y_261_ = v___y_274_;
v___y_262_ = v___y_275_;
v___y_263_ = v___y_276_;
v___y_264_ = v___y_277_;
goto v___jp_258_;
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_fvars_232_);
lean_dec(v_i_231_);
lean_dec_ref(v_entries_230_);
lean_dec_ref(v_k_229_);
v_a_299_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_278_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_278_);
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
}
}
}
v___jp_238_:
{
lean_object* v___f_246_; lean_object* v___x_247_; 
v___f_246_ = lean_alloc_closure((void*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_246_, 0, v_i_231_);
lean_closure_set(v___f_246_, 1, v_e_240_);
lean_closure_set(v___f_246_, 2, v_entries_230_);
lean_closure_set(v___f_246_, 3, v_fvars_232_);
lean_closure_set(v___f_246_, 4, v_k_229_);
v___x_247_ = l_Lean_Core_mkFreshUserName(v_baseUserName_239_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v___x_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref_known(v___x_247_, 1);
v___x_249_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_a_248_, v_type_241_, v___f_246_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_249_;
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v___f_246_);
lean_dec_ref(v_type_241_);
v_a_250_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_247_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_247_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
v___jp_258_:
{
lean_object* v___x_265_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1));
v_baseUserName_239_ = v___x_265_;
v_e_240_ = v___y_260_;
v_type_241_ = v___y_259_;
v___y_242_ = v___y_261_;
v___y_243_ = v___y_262_;
v___y_244_ = v___y_263_;
v___y_245_ = v___y_264_;
goto v___jp_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(lean_object* v_i_323_, lean_object* v_e_324_, lean_object* v_entries_325_, lean_object* v_fvars_326_, lean_object* v_k_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_i_323_, v___x_334_);
lean_inc(v___x_335_);
v___x_336_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(v_e_324_, v_x_328_, v_entries_325_, v___x_335_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v___x_338_ = lean_array_push(v_fvars_326_, v_x_328_);
v___x_339_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_327_, v_a_337_, v___x_335_, v___x_338_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_339_;
}
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
lean_dec(v___x_335_);
lean_dec_ref(v_x_328_);
lean_dec_ref(v_k_327_);
lean_dec_ref(v_fvars_326_);
v_a_340_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_336_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_336_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(lean_object* v_k_348_, lean_object* v_entries_349_, lean_object* v_i_350_, lean_object* v_fvars_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_348_, v_entries_349_, v_i_350_, v_fvars_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(lean_object* v_00_u03b1_358_, lean_object* v_k_359_, lean_object* v_entries_360_, lean_object* v_i_361_, lean_object* v_fvars_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_359_, v_entries_360_, v_i_361_, v_fvars_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(lean_object* v_00_u03b1_369_, lean_object* v_k_370_, lean_object* v_entries_371_, lean_object* v_i_372_, lean_object* v_fvars_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(v_00_u03b1_369_, v_k_370_, v_entries_371_, v_i_372_, v_fvars_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(lean_object* v_00_u03b1_380_, lean_object* v_name_381_, uint8_t v_bi_382_, lean_object* v_type_383_, lean_object* v_k_384_, uint8_t v_kind_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_381_, v_bi_382_, v_type_383_, v_k_384_, v_kind_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(lean_object* v_00_u03b1_392_, lean_object* v_name_393_, lean_object* v_bi_394_, lean_object* v_type_395_, lean_object* v_k_396_, lean_object* v_kind_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v_bi_boxed_403_; uint8_t v_kind_boxed_404_; lean_object* v_res_405_; 
v_bi_boxed_403_ = lean_unbox(v_bi_394_);
v_kind_boxed_404_ = lean_unbox(v_kind_397_);
v_res_405_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(v_00_u03b1_392_, v_name_393_, v_bi_boxed_403_, v_type_395_, v_k_396_, v_kind_boxed_404_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(lean_object* v_00_u03b1_406_, lean_object* v_name_407_, lean_object* v_type_408_, lean_object* v_k_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_407_, v_type_408_, v_k_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(lean_object* v_00_u03b1_416_, lean_object* v_name_417_, lean_object* v_type_418_, lean_object* v_k_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(v_00_u03b1_416_, v_name_417_, v_type_418_, v_k_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(lean_object* v_00_u03b1_426_, lean_object* v_msg_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(lean_object* v_00_u03b1_434_, lean_object* v_msg_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(v_00_u03b1_434_, v_msg_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(lean_object* v_e_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = l_Lean_Expr_hasMVar(v_e_442_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v_e_442_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v_mctx_448_; lean_object* v___x_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_452_; lean_object* v_cache_453_; lean_object* v_zetaDeltaFVarIds_454_; lean_object* v_postponed_455_; lean_object* v_diag_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_465_; 
v___x_447_ = lean_st_ref_get(v___y_443_);
v_mctx_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_mctx_448_);
lean_dec(v___x_447_);
v___x_449_ = l_Lean_instantiateMVarsCore(v_mctx_448_, v_e_442_);
v_fst_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_fst_450_);
v_snd_451_ = lean_ctor_get(v___x_449_, 1);
lean_inc(v_snd_451_);
lean_dec_ref(v___x_449_);
v___x_452_ = lean_st_ref_take(v___y_443_);
v_cache_453_ = lean_ctor_get(v___x_452_, 1);
v_zetaDeltaFVarIds_454_ = lean_ctor_get(v___x_452_, 2);
v_postponed_455_ = lean_ctor_get(v___x_452_, 3);
v_diag_456_ = lean_ctor_get(v___x_452_, 4);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v___x_452_, 0);
lean_dec(v_unused_466_);
v___x_458_ = v___x_452_;
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_diag_456_);
lean_inc(v_postponed_455_);
lean_inc(v_zetaDeltaFVarIds_454_);
lean_inc(v_cache_453_);
lean_dec(v___x_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_465_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v_snd_451_);
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_snd_451_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_cache_453_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_zetaDeltaFVarIds_454_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_postponed_455_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_diag_456_);
v___x_461_ = v_reuseFailAlloc_464_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_st_ref_put(v___y_443_, v___x_461_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_fst_450_);
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(lean_object* v_e_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_467_, v___y_468_);
lean_dec(v___y_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(lean_object* v_e_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_e_471_, v___y_473_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(lean_object* v_e_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(v_e_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(size_t v_sz_485_, size_t v_i_486_, lean_object* v_bs_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_usize_dec_lt(v_i_486_, v_sz_485_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v_bs_487_);
return v___x_494_;
}
else
{
lean_object* v_v_495_; lean_object* v___x_496_; lean_object* v_bs_x27_497_; lean_object* v___x_498_; 
v_v_495_ = lean_array_uget(v_bs_487_, v_i_486_);
v___x_496_ = lean_unsigned_to_nat(0u);
v_bs_x27_497_ = lean_array_uset(v_bs_487_, v_i_486_, v___x_496_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
lean_inc(v_v_495_);
v___x_498_ = lean_infer_type(v_v_495_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v___x_500_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_a_499_, v___y_489_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; uint8_t v___x_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = 0;
v___x_503_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_503_, 0, v_v_495_);
lean_ctor_set(v___x_503_, 1, v_a_501_);
lean_ctor_set_uint8(v___x_503_, sizeof(void*)*2, v___x_502_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_486_, v___x_504_);
v___x_506_ = lean_array_uset(v_bs_x27_497_, v_i_486_, v___x_503_);
v_i_486_ = v___x_505_;
v_bs_487_ = v___x_506_;
goto _start;
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v_bs_x27_497_);
lean_dec(v_v_495_);
v_a_508_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_500_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_500_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_bs_x27_497_);
lean_dec(v_v_495_);
v_a_516_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_498_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_498_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(lean_object* v_sz_524_, lean_object* v_i_525_, lean_object* v_bs_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
size_t v_sz_boxed_532_; size_t v_i_boxed_533_; lean_object* v_res_534_; 
v_sz_boxed_532_ = lean_unbox_usize(v_sz_524_);
lean_dec(v_sz_524_);
v_i_boxed_533_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_boxed_532_, v_i_boxed_533_, v_bs_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg(lean_object* v_es_537_, lean_object* v_k_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
size_t v_sz_544_; size_t v___x_545_; lean_object* v___x_546_; 
v_sz_544_ = lean_array_size(v_es_537_);
v___x_545_ = ((size_t)0ULL);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_544_, v___x_545_, v_es_537_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = ((lean_object*)(l_Lean_Meta_generalizeTelescope___redArg___closed__0));
v___x_550_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(v_k_538_, v_a_547_, v___x_548_, v___x_549_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v___x_550_;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec_ref(v_k_538_);
v_a_551_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_546_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_546_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___redArg___boxed(lean_object* v_es_559_, lean_object* v_k_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_559_, v_k_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope(lean_object* v_00_u03b1_567_, lean_object* v_es_568_, lean_object* v_k_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_generalizeTelescope___redArg(v_es_568_, v_k_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generalizeTelescope___boxed(lean_object* v_00_u03b1_576_, lean_object* v_es_577_, lean_object* v_k_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_generalizeTelescope(v_00_u03b1_576_, v_es_577_, v_k_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_584_;
}
}
lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_GeneralizeTelescope(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
